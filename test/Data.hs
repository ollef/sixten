data Bool where
  True : Bool
  False : Bool

data List a where
  Nil : List a
  Cons : a -> List a -> List a

tt = True
nil = Nil
list : boolList
list = Cons False (Cons True Nil)
boolList = List Bool

test b = case b of
  False -> 0
  True -> 1
