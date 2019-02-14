{-# LANGUAGE BangPatterns #-}
module Elaboration.TypeCheck.Literal where

import Protolude

import Data.ByteString as ByteString
import Data.HashSet(HashSet)
import qualified Data.HashSet as HashSet
import Data.Text(Text)
import Data.Text.Encoding as Encoding
import Numeric.Natural

import qualified Builtin.Names as Builtin
import Syntax
import qualified Syntax.Core as Core
import qualified Syntax.Literal as Core
import qualified Syntax.Pre.Literal as Pre
import qualified Syntax.Pre.Pattern as Pre
import Util

inferLit :: Pre.Literal -> (Core.Expr m v, Core.Expr m v)
inferLit (Pre.Integer i) = (Core.Lit $ Core.Integer i, Builtin.IntType)
inferLit (Pre.String s) = (string s, Builtin.StringType)

inferCoreLit :: Core.Literal -> Core.Expr m v
inferCoreLit (Core.Integer _) = Builtin.IntType
inferCoreLit (Core.Natural _) = Builtin.Nat
inferCoreLit (Core.Byte _) = Builtin.ByteType
inferCoreLit (Core.TypeRep _) = Builtin.Type

litPat :: Pre.Literal -> Pre.Pat (HashSet QConstr) Core.Literal typ v
litPat (Pre.Integer i) = Pre.LitPat (Core.Integer i)
litPat (Pre.String s) = stringPat s

string :: Text -> Core.Expr m v
string s
  = Core.apps
    (Core.Con Builtin.MkStringConstr)
    [(Explicit, byteArray $ Encoding.encodeUtf8 s)]

stringPat :: Text -> Pre.Pat (HashSet QConstr) Core.Literal typ v
stringPat s
  = Pre.ConPat
    (HashSet.singleton Builtin.MkStringConstr)
    (toVector [(Explicit, byteArrayPat $ Encoding.encodeUtf8 s)])

byteArray :: ByteString -> Core.Expr m v
byteArray bs
  = Core.apps (Core.Con Builtin.MkArrayConstr)
  [ (Implicit, Builtin.ByteType)
  , (Explicit, lenExpr)
  , ( Explicit
    , Core.apps (Core.Con Builtin.Ref)
      [ (Implicit, byteVectorType lenExpr)
      , ( Explicit
        , fst $ ByteString.foldr go (Core.Con Builtin.MkUnitConstr, 0) bs
        )
      ]
    )
  ]
  where
    lenExpr = nat len
    len = fromIntegral $ ByteString.length bs
    go byte (rest, !i) =
      ( Core.apps (Core.Con Builtin.MkPairConstr)
        [ (Implicit, Builtin.ByteType)
        , (Implicit, byteVectorType $ nat i)
        , (Explicit, Core.Lit $ Core.Byte byte)
        , (Explicit, rest)
        ]
      , i + 1
      )

byteArrayPat :: ByteString -> Pre.Pat (HashSet QConstr) Core.Literal typ v
byteArrayPat bs
  = Pre.ConPat (HashSet.singleton Builtin.MkArrayConstr)
  (toVector
    [ (Explicit, natPat len)
    , ( Explicit
      , Pre.ConPat (HashSet.singleton Builtin.Ref)
        (toVector
          [ ( Explicit
            , ByteString.foldr go (Pre.ConPat (HashSet.singleton Builtin.MkUnitConstr) mempty) bs
            )
          ]
        )
      )
    ]
  )
  where
    len = fromIntegral $ ByteString.length bs
    go byte rest =
      Pre.ConPat (HashSet.singleton Builtin.MkPairConstr)
        (toVector
          [ (Explicit, Pre.LitPat $ Core.Byte byte)
          , (Explicit, rest)
          ])

byteArrayType :: Core.Expr m v
byteArrayType = Core.App (global $ GName Builtin.ArrayName mempty) Explicit Builtin.ByteType

ptrType :: Core.Expr m v -> Core.Expr m v
ptrType = Core.App (global $ GName Builtin.PtrName mempty) Explicit

byteVectorType :: Core.Expr m v -> Core.Expr m v
byteVectorType len = Core.apps
  (global $ GName Builtin.VectorName mempty)
  [ (Explicit, len)
  , (Explicit, Builtin.ByteType)
  ]

nat :: Natural -> Core.Expr m v
nat = Core.Lit . Core.Natural

natPat :: Natural -> Pre.Pat c Core.Literal typ v'
natPat = Pre.LitPat . Core.Natural
