// HIGHLIGHT: INFORMATION
// FIX: Replace 'if' expression with safe cast expression

interface Foo
interface Bar : Foo

data class Data(val foo: Foo)

fun handle(data: Data) {
    val bar = <caret>if (data.foo is Bar) data.foo else null
}