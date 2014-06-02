module Util where
import Bound

type Scope1 = Scope ()
type Name = String

data Plicitness = Implicit | Explicit
  deriving (Eq, Ord, Show)
