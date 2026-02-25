$
  L ::=& top | bot | L_1 \& L_2 | l \ 
  K ::=& ast | K -> ast | forall l : "L"[L_1, L_2]. space K \
  T ::=& "Base" | T -> T | forall alpha: K. space T
    | forall l : "L"[L_1, L_2]. space T
    | { f_i : T_i | i }
    | alpha \
  e ::=& x | e : T | e_1 space e_2 | e space T | e space l\
   |& Lambda alpha: K. space e\
   |& Lambda l: "L". space e\
   |& lambda x: T. space e "where" T : ast\ 
   |& { f_i = e_i | i} \
   |& e.f_i
$

subkinding relation from lifetime-polymorphic kinds (contravariant)

shorthand: $[|T_l|] = lambda l'. [|T|](l \& l')$

Need to add:
- subtyping
- variance

```
fun <T> id(local x: T): T_{x} = x
```

$
  Lambda l_c : "L". space
  Lambda T : -"L" -> ast. space
  Lambda l_x : "L". space
  lambda x : T_(l_x). space
  x : T_(l_x)
$

shorthand: $-"L" -> ast = forall "L"[bot, top]. space ast$

Note: $l_c <: l_x$

```
local class C<l>() {
  val impl: Impl_{this}
  fun_{global} f()
  fun_{l} g()
  fun_{this} h()
}
```

$
C = 
forall l_"this" : "L". space
forall l : "L". space
{&\
  &quad&&f :
    forall l_c : L[bot, top]. space ()  \
  &&&g :
    forall l_c : L[bot, l]. space ()  \
  &&&h :
    forall l_c : L[bot, l_"this"]. space ()  \
}&\
$

```
var c: C<l_a>_{l_d}
run {
  c = C<l_a>(/* depend on run */)
}

// later, in lifetime l_u
c.h()
```

$
  [|c.h()|] = [|c|].h space l_u
$

#pagebreak()
```kotlin
fun f(): T {
  lateinit var result: T
  val builder : ResultBuilder_{result} =
    ResultBuilder { result = it }
  builder.build()
  return result
}
```