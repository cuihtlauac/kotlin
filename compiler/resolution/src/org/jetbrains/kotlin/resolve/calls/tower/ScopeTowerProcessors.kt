/*
 * Copyright 2010-2016 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.jetbrains.kotlin.resolve.calls.tower

import org.jetbrains.kotlin.name.Name
import org.jetbrains.kotlin.resolve.calls.tasks.ExplicitReceiverKind
import org.jetbrains.kotlin.resolve.scopes.receivers.DetailedReceiver
import org.jetbrains.kotlin.resolve.scopes.receivers.QualifierReceiver
import org.jetbrains.kotlin.resolve.scopes.receivers.ReceiverValueWithSmartCastInfo


class KnownResultProcessor<out C : Candidate>(
    val result: Collection<C>
) : ScopeTowerProcessor<C> {
    override fun process(data: TowerData) = if (data == TowerData.Empty) listOfNotNull(result.takeIf { it.isNotEmpty() }) else emptyList()

    override fun recordLookups(skippedData: Collection<TowerData>, name: Name) {}
}

// use this if processors priority is important
class PrioritizedCompositeScopeTowerProcessor<out C : Candidate>(
    vararg val processors: ScopeTowerProcessor<C>
) : ScopeTowerProcessor<C> {
    override fun process(data: TowerData): List<Collection<C>> = processors.flatMap { it.process(data) }

    override fun recordLookups(skippedData: Collection<TowerData>, name: Name) {
        processors.forEach { it.recordLookups(skippedData, name) }
    }
    companion object {
        fun <C : Candidate> aggreagate(
            vararg toProcessors: (ImplicitScopeTower, CandidateFactory<C>, DetailedReceiver?, Boolean)->ScopeTowerProcessor<C>
        ) = {
            scopeTower: ImplicitScopeTower,
            context: CandidateFactory<C>,
            explicitReceiver: DetailedReceiver?,
            classValueReceiver: Boolean
        ->
            PrioritizedCompositeScopeTowerProcessor<C>(
                *toProcessors.map { it(scopeTower, context, explicitReceiver, classValueReceiver) }.toTypedArray()
            )
        }
    }
}

// use this if all processors has same priority
class SamePriorityCompositeScopeTowerProcessor<out C : Candidate>(
    private vararg val processors: SimpleScopeTowerProcessor<C>
) : SimpleScopeTowerProcessor<C> {
    override fun simpleProcess(data: TowerData): Collection<C> = processors.flatMap { it.simpleProcess(data) }
    override fun recordLookups(skippedData: Collection<TowerData>, name: Name) {
        processors.forEach { it.recordLookups(skippedData, name) }
    }
    companion object {
        fun <C : Candidate> aggreagate(
            vararg toProcessors: (ImplicitScopeTower, CandidateFactory<C>, DetailedReceiver?)->SimpleScopeTowerProcessor<C>
        ) = {
            scopeTower: ImplicitScopeTower,
            context: CandidateFactory<C>,
            explicitReceiver: DetailedReceiver?
        ->
            SamePriorityCompositeScopeTowerProcessor<C>(
                *toProcessors.map { it(scopeTower, context, explicitReceiver) }.toTypedArray()
            )
        }
    }
}

interface SimpleScopeTowerProcessor<out C : Candidate> : ScopeTowerProcessor<C> {
    fun simpleProcess(data: TowerData): Collection<C>

    override fun process(data: TowerData): List<Collection<C>> = listOfNotNull(simpleProcess(data).takeIf { it.isNotEmpty() })
}

internal abstract class AbstractSimpleScopeTowerProcessor<C : Candidate>(
    val candidateFactory: CandidateFactory<C>
) : SimpleScopeTowerProcessor<C> {
    fun createCandidates(
        collector: Collection<CandidateWithBoundDispatchReceiver>,
        kind: ExplicitReceiverKind,
        receiver: ReceiverValueWithSmartCastInfo?
    ) : Collection<C> {
        val result = mutableListOf<C>()
        for (candidate in collector) {
            if (candidate.requiresExtensionReceiver == (receiver != null)) {
                result.add(
                    candidateFactory.createCandidate(
                        candidate,
                        kind,
                        extensionReceiver = receiver
                    )
                )
            }
        }
        return result
    }
}

private typealias CandidatesCollector =
        ScopeTowerLevel.(extensionReceiver: ReceiverValueWithSmartCastInfo?) -> Collection<CandidateWithBoundDispatchReceiver>

internal class ExplicitReceiverScopeTowerProcessor<C : Candidate>(
    val scopeTower: ImplicitScopeTower,
    context: CandidateFactory<C>,
    val explicitReceiver: ReceiverValueWithSmartCastInfo,
    val collectCandidates: CandidatesCollector
) : AbstractSimpleScopeTowerProcessor<C>(context) {
    override fun simpleProcess(data: TowerData): Collection<C> {
        return when (data) {
            TowerData.Empty -> createCandidates(
                MemberScopeTowerLevel(scopeTower, explicitReceiver).collectCandidates(null),
                ExplicitReceiverKind.DISPATCH_RECEIVER,
                null
            )
            is TowerData.TowerLevel -> createCandidates(
                data.level.collectCandidates(explicitReceiver),
                ExplicitReceiverKind.EXTENSION_RECEIVER,
                explicitReceiver
            )
            else -> emptyList()
        }
    }

    override fun recordLookups(skippedData: Collection<TowerData>, name: Name) {
        for (data in skippedData) {
            if (data is TowerData.TowerLevel) {
                data.level.recordLookup(name)
            }
        }
    }
}

private class QualifierScopeTowerProcessor<C : Candidate>(
    val scopeTower: ImplicitScopeTower,
    context: CandidateFactory<C>,
    val qualifier: QualifierReceiver,
    val collectCandidates: CandidatesCollector
) : AbstractSimpleScopeTowerProcessor<C>(context) {
    override fun simpleProcess(data: TowerData): Collection<C> {
        if (data != TowerData.Empty) return emptyList()

        return createCandidates(
            QualifierScopeTowerLevel(scopeTower, qualifier).collectCandidates(null),
            ExplicitReceiverKind.NO_EXPLICIT_RECEIVER,
            null
        )
    }

    // QualifierScopeTowerProcessor works only with TowerData.Empty that should not be ignored
    override fun recordLookups(skippedData: Collection<TowerData>, name: Name) {}
}

private class NoExplicitReceiverScopeTowerProcessor<C : Candidate>(
    context: CandidateFactory<C>,
    val collectCandidates: CandidatesCollector
) : AbstractSimpleScopeTowerProcessor<C>(context) {
    override fun simpleProcess(data: TowerData): Collection<C> = when (data) {
        is TowerData.TowerLevel -> createCandidates(
            data.level.collectCandidates(null),
            ExplicitReceiverKind.NO_EXPLICIT_RECEIVER,
            null
        )
        is TowerData.BothTowerLevelAndImplicitReceiver -> createCandidates(
            data.level.collectCandidates(data.implicitReceiver),
            ExplicitReceiverKind.NO_EXPLICIT_RECEIVER,
            data.implicitReceiver
        )
        else -> emptyList()
    }

    override fun recordLookups(skippedData: Collection<TowerData>, name: Name) {
        for (data in skippedData) {
            when (data) {
                is TowerData.TowerLevel -> data.level.recordLookup(name)
                is TowerData.BothTowerLevelAndImplicitReceiver -> data.level.recordLookup(name)
                is TowerData.ForLookupForNoExplicitReceiver -> data.level.recordLookup(name)
            }
        }
    }
}

private fun <C : Candidate> createSimpleProcessorWithoutClassValueReceiver(
    scopeTower: ImplicitScopeTower,
    context: CandidateFactory<C>,
    explicitReceiver: DetailedReceiver?,
    collectCandidates: CandidatesCollector
): SimpleScopeTowerProcessor<C> =
    when (explicitReceiver) {
        is ReceiverValueWithSmartCastInfo -> ExplicitReceiverScopeTowerProcessor(scopeTower, context, explicitReceiver, collectCandidates)
        is QualifierReceiver -> QualifierScopeTowerProcessor(scopeTower, context, explicitReceiver, collectCandidates)
        else -> {
            assert(explicitReceiver == null) {
                "Illegal explicit receiver: $explicitReceiver(${explicitReceiver!!::class.java.simpleName})"
            }
            NoExplicitReceiverScopeTowerProcessor(context, collectCandidates)
        }
    }

private fun <C : Candidate> createSimpleProcessorWithoutClassValueReceiver(collectCandidates: CandidatesCollector)
    = {
        scopeTower: ImplicitScopeTower,
        context: CandidateFactory<C>,
        explicitReceiver: DetailedReceiver?
    ->
        createSimpleProcessorWithoutClassValueReceiver(scopeTower, context, explicitReceiver, collectCandidates)
    }


private fun <C : Candidate> createSimpleProcessor(
    scopeTower: ImplicitScopeTower,
    context: CandidateFactory<C>,
    explicitReceiver: DetailedReceiver?,
    classValueReceiver: Boolean,
    collectCandidates: CandidatesCollector
): ScopeTowerProcessor<C> {
    val withoutClassValueProcessor =
        createSimpleProcessorWithoutClassValueReceiver(scopeTower, context, explicitReceiver, collectCandidates)

    if (classValueReceiver && explicitReceiver is QualifierReceiver) {
        val classValue = explicitReceiver.classValueReceiverWithSmartCastInfo ?: return withoutClassValueProcessor
        return PrioritizedCompositeScopeTowerProcessor(
            withoutClassValueProcessor,
            ExplicitReceiverScopeTowerProcessor(scopeTower, context, classValue, collectCandidates)
        )
    }
    return withoutClassValueProcessor
}

private fun <C : Candidate> createSimpleProcessor(collectCandidates: CandidatesCollector)
    = {
        scopeTower: ImplicitScopeTower,
        context: CandidateFactory<C>,
        explicitReceiver: DetailedReceiver?,
        classValueReceiver: Boolean
    ->
        createSimpleProcessor(scopeTower, context, explicitReceiver, classValueReceiver, collectCandidates)
    }

fun <C : Candidate> createCallableReferenceProcessor(name: Name) = SamePriorityCompositeScopeTowerProcessor.aggreagate (
    createSimpleProcessorWithoutClassValueReceiver { getVariables(name, it) },
    createSimpleProcessorWithoutClassValueReceiver { getFunctions(name, it) }
) as SamePriorityCompositeScopeTowerProcessor<C>

fun <C : Candidate> createVariableProcessor(name: Name) = createSimpleProcessor<C> { getVariables(name, it) }

fun <C : Candidate> createVariableAndObjectProcessor(name: Name) =
    PrioritizedCompositeScopeTowerProcessor.aggreagate(
        createVariableProcessor<C>(name),
        createSimpleProcessor<C> { getObjects(name, it) }
    )

fun <C : Candidate> createSimpleFunctionProcessor(name: Name) = createSimpleProcessor<C> { getFunctions(name, it) }

fun <C : Candidate> createFunctionProcessor(
    name: Name,
    factoryProviderForInvoke: CandidateFactoryProviderForInvoke<C>
) =
    PrioritizedCompositeScopeTowerProcessor.aggreagate(
        // a.foo() -- simple function call
        createSimpleFunctionProcessor(name),
        // a.foo() -- property a.foo + foo.invoke()
        {
            scopeTower: ImplicitScopeTower,
            _: CandidateFactory<C>,
            explicitReceiver: DetailedReceiver?,
            _: Boolean
        ->
            InvokeTowerProcessor(scopeTower, name, factoryProviderForInvoke, explicitReceiver)
        },
        // a.foo() -- property foo is extension function with receiver a -- a.invoke()
        {
            scopeTower: ImplicitScopeTower,
            _: CandidateFactory<C>,
            explicitReceiver: DetailedReceiver?,
            _: Boolean
        ->
            createProcessorWithReceiverValueOrEmpty(explicitReceiver) {
                InvokeExtensionTowerProcessor(scopeTower, name, factoryProviderForInvoke, it)
            }
        }
    )

fun <C : Candidate> createProcessorWithReceiverValueOrEmpty(
    explicitReceiver: DetailedReceiver?,
    create: (ReceiverValueWithSmartCastInfo?) -> ScopeTowerProcessor<C>
): ScopeTowerProcessor<C> {
    return if (explicitReceiver is QualifierReceiver) {
        explicitReceiver.classValueReceiverWithSmartCastInfo?.let(create)
                ?: KnownResultProcessor<C>(listOf())
    } else {
        create(explicitReceiver as ReceiverValueWithSmartCastInfo?)
    }
}
