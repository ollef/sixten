{-# LANGUAGE OverloadedStrings #-}
module Syntax.Concrete.Literal where

import Data.ByteString as ByteString
import Data.Text(Text)
import Data.Text.Encoding as Encoding
import qualified Data.Vector as Vector

import Syntax
import Syntax.Concrete.Pattern
import Syntax.Concrete.Unscoped as Unscoped

import qualified Builtin

-- TODO don't use unqualified
string :: Text -> Expr QName
string
  = App (Var $ unqualified $ constrToName Builtin.MkStringName) Explicit
  . byteArray
  . Encoding.encodeUtf8

byteArray :: ByteString -> Expr QName
byteArray bs
  = Unscoped.apps (Var $ unqualified $ constrToName Builtin.MkArrayName)
  [ (Explicit, nat $ ByteString.length bs)
  , ( Explicit
    , App (Var $ unqualified $ constrToName Builtin.RefName) Explicit
    $ ByteString.foldr
      (\byte rest -> Unscoped.apps (Var $ unqualified $ constrToName Builtin.MkPairName) [(Explicit, Lit $ Byte byte), (Explicit, rest)])
      (Var $ unqualified $ constrToName Builtin.MkUnitConstrName)
      bs
    )
  ]

nat :: (Eq a, Num a) => a -> Expr QName
nat 0 = Var $ unqualified $ constrToName Builtin.ZeroName
nat n = App (Var $ unqualified $ constrToName Builtin.SuccName) Explicit (nat (n - 1))

stringPat :: Text -> Pat t v
stringPat
  = ConPat (Right Builtin.MkStringConstr)
  . pure
  . (,) Explicit
  . byteArrayPat
  . Encoding.encodeUtf8

byteArrayPat :: ByteString -> Pat t v
byteArrayPat bs = ConPat (Right Builtin.MkArrayConstr)
  $ Vector.fromList
  [ (Explicit, natPat $ ByteString.length bs)
  , (Explicit
    , ConPat (Right Builtin.Ref)
    $ pure
    ( Explicit
    , ByteString.foldr
      (\byte rest -> ConPat
        (Right Builtin.MkPairConstr)
        $ Vector.fromList [(Explicit, LitPat $ Byte byte), (Explicit, rest)])
      (ConPat (Right Builtin.MkUnitConstr) mempty)
      bs
    )
    )
  ]

natPat :: (Eq a, Num a) => a -> Pat t v
natPat 0 = ConPat (Right Builtin.ZeroConstr) mempty
natPat n = ConPat (Right Builtin.SuccConstr) $ pure (Explicit, natPat (n - 1))
