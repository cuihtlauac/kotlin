/*
 * Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license
 * that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.idea.inspections

import com.intellij.codeInspection.*
import com.intellij.openapi.application.ApplicationManager
import com.intellij.openapi.fileEditor.FileEditorManager
import com.intellij.openapi.project.Project
import com.intellij.psi.PsiDocumentManager
import com.intellij.psi.PsiElementVisitor
import com.intellij.psi.SmartPsiElementPointer
import com.intellij.refactoring.rename.inplace.VariableInplaceRenameHandler
import org.jetbrains.kotlin.descriptors.SimpleFunctionDescriptor
import org.jetbrains.kotlin.descriptors.ValueParameterDescriptor
import org.jetbrains.kotlin.idea.caches.resolve.analyze
import org.jetbrains.kotlin.idea.core.ShortenReferences
import org.jetbrains.kotlin.idea.references.resolveMainReferenceToDescriptors
import org.jetbrains.kotlin.idea.util.getReceiverTargetDescriptor
import org.jetbrains.kotlin.idea.util.getResolutionScope
import org.jetbrains.kotlin.incremental.components.NoLookupLocation
import org.jetbrains.kotlin.name.Name
import org.jetbrains.kotlin.psi.*
import org.jetbrains.kotlin.psi.psiUtil.createSmartPointer
import org.jetbrains.kotlin.psi.psiUtil.endOffset
import org.jetbrains.kotlin.psi.psiUtil.getOrCreateParameterList
import org.jetbrains.kotlin.psi.psiUtil.startOffset
import org.jetbrains.kotlin.resolve.BindingContext
import org.jetbrains.kotlin.resolve.BindingContext.FUNCTION
import org.jetbrains.kotlin.resolve.calls.callUtil.getResolvedCall
import org.jetbrains.kotlin.resolve.descriptorUtil.fqNameSafe
import org.jetbrains.kotlin.resolve.lazy.BodyResolveMode
import org.jetbrains.kotlin.resolve.scopes.LexicalScope
import org.jetbrains.kotlin.resolve.scopes.utils.collectDescriptorsFiltered
import org.jetbrains.kotlin.resolve.scopes.utils.findVariable

private val counterpartNames = mapOf(
    "apply" to "also",
    "run" to "let",
    "let" to "run"
)

class ScopeFunctionConversionInspection : AbstractKotlinInspection() {
    override fun buildVisitor(holder: ProblemsHolder, isOnTheFly: Boolean, session: LocalInspectionToolSession): PsiElementVisitor {
        return callExpressionVisitor { expression ->
            val counterpartName = getCounterpart(expression)
            if (counterpartName != null) {
                holder.registerProblem(
                    expression.calleeExpression!!,
                    "Call can be replaced with another scope function",
                    ProblemHighlightType.INFORMATION,
                    if (counterpartName == "also" || counterpartName == "let")
                        ConvertScopeFunctionToParameter(counterpartName)
                    else
                        ConvertScopeFunctionToReceiver(counterpartName)
                )
            }

        }
    }
}

private fun getCounterpart(expression: KtCallExpression): String? {
    val callee = expression.calleeExpression as? KtNameReferenceExpression ?: return null
    val calleeName = callee.getReferencedName()
    val counterpartName = counterpartNames[calleeName]
    val lambdaArgument = expression.lambdaArguments.singleOrNull()
    if (counterpartName != null && lambdaArgument != null) {
        if (lambdaArgument.getLambdaExpression().valueParameters.isNotEmpty()) {
            return null
        }
        val bindingContext = callee.analyze(BodyResolveMode.PARTIAL)
        val resolvedCall = callee.getResolvedCall(bindingContext) ?: return null
        if (resolvedCall.resultingDescriptor.fqNameSafe.asString() == "kotlin.$calleeName" &&
            nameResolvesToStdlib(expression, bindingContext, counterpartName)
        ) {
            return counterpartName
        }
    }
    return null
}

private fun nameResolvesToStdlib(expression: KtCallExpression, bindingContext: BindingContext, name: String): Boolean {
    val scope = expression.getResolutionScope(bindingContext) ?: return true
    val descriptors = scope.collectDescriptorsFiltered(nameFilter = { it.asString() == name })
    return descriptors.isNotEmpty() && descriptors.all { it.fqNameSafe.asString() == "kotlin.$name" }
}

abstract class ConvertScopeFunctionFix(private val counterpartName: String) : LocalQuickFix {
    override fun getFamilyName() = "Convert to '$counterpartName'"

    override fun applyFix(project: Project, problemDescriptor: ProblemDescriptor) {
        val callee = problemDescriptor.psiElement as KtNameReferenceExpression
        val callExpression = callee.parent as? KtCallExpression ?: return
        val bindingContext = callExpression.analyze()

        val lambda = callExpression.lambdaArguments.firstOrNull() ?: return
        val functionLiteral = lambda.getLambdaExpression().functionLiteral
        val lambdaDescriptor = bindingContext[FUNCTION, functionLiteral] ?: return

        val parameterToRename = updateLambda(bindingContext, lambda, lambdaDescriptor)
        callee.replace(KtPsiFactory(project).createExpression(counterpartName) as KtNameReferenceExpression)
        postprocessLambda(lambda)

        if (parameterToRename != null && !ApplicationManager.getApplication().isUnitTestMode) {
            parameterToRename.startInPlaceRename()
        }
    }

    protected abstract fun postprocessLambda(lambda: KtLambdaArgument)

    protected abstract fun updateLambda(
        bindingContext: BindingContext,
        lambda: KtLambdaArgument,
        lambdaDescriptor: SimpleFunctionDescriptor
    ): KtElement?
}

class ConvertScopeFunctionToParameter(counterpartName: String) : ConvertScopeFunctionFix(counterpartName) {
    override fun updateLambda(
        bindingContext: BindingContext,
        lambda: KtLambdaArgument,
        lambdaDescriptor: SimpleFunctionDescriptor
    ): KtElement? {
        return replaceThisWithIt(bindingContext, lambda, lambdaDescriptor)
    }

    override fun postprocessLambda(lambda: KtLambdaArgument) {
        ShortenReferences { ShortenReferences.Options(removeThisLabels = true) }.process(lambda) { element ->
            if (element is KtThisExpression && element.getLabelName() != null)
                ShortenReferences.FilterResult.PROCESS
            else
                ShortenReferences.FilterResult.GO_INSIDE
        }
    }
}

class ConvertScopeFunctionToReceiver(counterpartName: String) : ConvertScopeFunctionFix(counterpartName) {
    override fun updateLambda(
        bindingContext: BindingContext,
        lambda: KtLambdaArgument,
        lambdaDescriptor: SimpleFunctionDescriptor
    ): KtElement? {
        val itUsagesToReplace = mutableListOf<SmartPsiElementPointer<KtSimpleNameExpression>>()
        val thisUsagesToQualify = mutableListOf<Pair<SmartPsiElementPointer<KtThisExpression>, String>>()

        lambda.accept(object : KtTreeVisitorVoid() {
            override fun visitSimpleNameExpression(expression: KtSimpleNameExpression) {
                super.visitSimpleNameExpression(expression)
                if (expression.getReferencedName() == "it") {
                    val result = expression.resolveMainReferenceToDescriptors().singleOrNull()
                    if (result is ValueParameterDescriptor && result.containingDeclaration == lambdaDescriptor) {
                        itUsagesToReplace.add(expression.createSmartPointer())
                    }
                }
            }

            override fun visitThisExpression(expression: KtThisExpression) {
                val resolvedCall = expression.getResolvedCall(bindingContext) ?: return
                val qualifierName = resolvedCall.resultingDescriptor.containingDeclaration.name
                thisUsagesToQualify.add(expression.createSmartPointer() to qualifierName.asString())
            }
        })

        val project = lambda.project
        val factory = KtPsiFactory(project)
        for ((thisPointer, qualifier) in thisUsagesToQualify) {
            thisPointer.element?.replace(factory.createThisExpression(qualifier))
        }
        for (itPointer in itUsagesToReplace) {
            itPointer.element?.replace(factory.createThisExpression())
        }
        return null
    }

    override fun postprocessLambda(lambda: KtLambdaArgument) {
        ShortenReferences { ShortenReferences.Options(removeThis = true) }.process(lambda) { element ->
            if (element is KtQualifiedExpression && element.receiverExpression is KtThisExpression)
                ShortenReferences.FilterResult.PROCESS
            else
                ShortenReferences.FilterResult.GO_INSIDE
        }
    }
}

private fun replaceThisWithIt(
    bindingContext: BindingContext,
    lambdaArgument: KtLambdaArgument,
    lambdaDescriptor: SimpleFunctionDescriptor
): KtParameter? {
    val project = lambdaArgument.project
    val factory = KtPsiFactory(project)
    val functionLiteral = lambdaArgument.getLambdaExpression().functionLiteral
    val lambdaExtensionReceiver = lambdaDescriptor.extensionReceiverParameter
    val lambdaDispatchReceiver = lambdaDescriptor.dispatchReceiverParameter

    var parameterName = "it"
    var parameterToRename: KtParameter? = null
    val scopes = mutableSetOf<LexicalScope>()
    if (needUniqueNameForParameter(lambdaArgument, scopes)) {
        parameterName = findUniqueParameterName(scopes)
    }

    val callsToReplace = mutableListOf<SmartPsiElementPointer<KtCallExpression>>()
    val nameReferencesToReplace = mutableListOf<SmartPsiElementPointer<KtSimpleNameExpression>>()
    val thisReferencesToReplace = mutableListOf<SmartPsiElementPointer<KtThisExpression>>()

    lambdaArgument.accept(object : KtTreeVisitorVoid() {
        override fun visitSimpleNameExpression(expression: KtSimpleNameExpression) {
            super.visitSimpleNameExpression(expression)
            val resolvedCall = expression.getResolvedCall(bindingContext) ?: return
            val dispatchReceiverTarget = resolvedCall.dispatchReceiver?.getReceiverTargetDescriptor(bindingContext)
            val extensionReceiverTarget = resolvedCall.extensionReceiver?.getReceiverTargetDescriptor(bindingContext)
            if (dispatchReceiverTarget == lambdaDescriptor || extensionReceiverTarget == lambdaDescriptor) {
                val parent = expression.parent
                if (parent is KtCallExpression && expression == parent.calleeExpression) {
                    callsToReplace.add(parent.createSmartPointer())
                } else if (parent is KtQualifiedExpression && parent.receiverExpression is KtThisExpression) {
                    // do nothing
                } else {
                    nameReferencesToReplace.add(expression.createSmartPointer())
                }
            }
        }

        override fun visitThisExpression(expression: KtThisExpression) {
            val resolvedCall = expression.getResolvedCall(bindingContext) ?: return
            if (resolvedCall.resultingDescriptor == lambdaDispatchReceiver ||
                resolvedCall.resultingDescriptor == lambdaExtensionReceiver) {
                thisReferencesToReplace.add(expression.createSmartPointer())
            }
        }
    })

    if (!callsToReplace.isEmpty() || !nameReferencesToReplace.isEmpty() || !thisReferencesToReplace.isEmpty()) {
        if (parameterName != "it") {
            val lambdaParameterList = functionLiteral.getOrCreateParameterList()
            val parameterToAdd = factory.createLambdaParameterList(parameterName).parameters.first()
            parameterToRename = lambdaParameterList.addParameterBefore(parameterToAdd, lambdaParameterList.parameters.firstOrNull())
        }

        // Calls need to be processed in outside-in order
        callsToReplace.sortBy { it.element!!.endOffset }

        for (namePointer in nameReferencesToReplace) {
            namePointer.element?.let { element ->
                element.replace(factory.createExpression("$parameterName.${element.getReferencedName()}"))
            }
        }
        for (thisPointer in thisReferencesToReplace) {
            thisPointer.element?.replace(factory.createExpression(parameterName))
        }
        for (callPointer in callsToReplace) {
            callPointer.element?.let { element ->
                element.replace(factory.createExpressionByPattern("$0.$1", parameterName, element))
            }
        }
    }

    return parameterToRename
}

private fun needUniqueNameForParameter(
    lambdaArgument: KtLambdaArgument,
    scopes: MutableSet<LexicalScope>
): Boolean {
    val resolutionScope = lambdaArgument.getResolutionScope()
    scopes.add(resolutionScope)
    var needUniqueName = false
    if (resolutionScope.findVariable(Name.identifier("it"), NoLookupLocation.FROM_IDE) != null) {
        needUniqueName = true
        // Don't return here - we still need to gather the list of nested scopes
    }

    lambdaArgument.accept(object : KtTreeVisitorVoid() {
        override fun visitDeclaration(dcl: KtDeclaration) {
            super.visitDeclaration(dcl)
            checkNeedUniqueName(dcl)
        }

        override fun visitLambdaExpression(lambdaExpression: KtLambdaExpression) {
            super.visitLambdaExpression(lambdaExpression)
            lambdaExpression.bodyExpression?.statements?.firstOrNull()?.let { checkNeedUniqueName(it) }
        }

        private fun checkNeedUniqueName(dcl: KtElement) {
            val nestedResolutionScope = dcl.getResolutionScope()
            scopes.add(nestedResolutionScope)
            if (nestedResolutionScope.findVariable(Name.identifier("it"), NoLookupLocation.FROM_IDE) != null) {
                needUniqueName = true
            }
        }
    })

    return needUniqueName
}

private fun KtElement.startInPlaceRename() {
    val project = project
    val document = containingFile.viewProvider.document ?: return
    val editor = FileEditorManager.getInstance(project).selectedTextEditor ?: return
    if (editor.document == document) {
        PsiDocumentManager.getInstance(project).doPostponedOperationsAndUnblockDocument(editor.document)

        editor.caretModel.moveToOffset(startOffset)
        VariableInplaceRenameHandler().doRename(this, editor, null)
    }
}

private fun findUniqueParameterName(resolutionScopes: Collection<LexicalScope>): String {
    var parameterName = "p"
    if (resolutionScopes.any { it.findVariable(Name.identifier(parameterName), NoLookupLocation.FROM_IDE) != null }) {
        for (index in generateSequence(0) { it + 1 }) {
            parameterName = "p$index"
            if (resolutionScopes.any { it.findVariable(Name.identifier(parameterName), NoLookupLocation.FROM_IDE) == null }) {
                break
            }
        }
    }
    return parameterName
}

