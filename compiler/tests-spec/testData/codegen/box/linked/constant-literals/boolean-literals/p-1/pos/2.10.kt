// HELPERS: REFLECT

/*
 * KOTLIN CODEGEN BOX SPEC TEST (POSITIVE)
 *
 * SECTIONS: constant-literals, boolean-literals
 * PARAGRAPH: 1
 * SENTENCE: [2] These are strong keywords which cannot be used as identifiers unless escaped.
 * NUMBER: 10
 * DESCRIPTION: The use of Boolean literals as the identifier (with backtick) in the companionObject.
 * NOTE: this test data is generated by FeatureInteractionTestDataGenerator. DO NOT MODIFY CODE MANUALLY!
 */

package org.jetbrains.`true`

open class A {
    companion object `false` {

    }
}

class B {
    companion object `true`: A() {

    }
}

fun box(): String? {
    if (!checkCompanionObjectName(A::class, "org.jetbrains.true.A.false")) return null
    if (!checkCompanionObjectName(B::class, "org.jetbrains.true.B.true")) return null

    return "OK"
}
