
ap1 : forall {m n}{A : Type {m}}{B : Type {n}}. (A -> B) -> A -> B
ap1 f x = f x

add3 : Size -> Size -> Size -> Size
add3 a b c = addSize (addSize a b) c

test = printSize (ap1 addSize 1 2)
test2 = printSize (ap1 (ap1 addSize 1) 2)
test3 = printSize (ap1 add3 1 2 3)
test4 = printSize (ap1 (ap1 add3 1) 2 3)
test5 = printSize (ap1 (ap1 (ap1 add3 1) 2) 3)
