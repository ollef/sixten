{-# LANGUAGE BangPatterns #-}
module Inference.TypeCheck.Literal where

import Data.ByteString as ByteString
import Data.Text(Text)
import Data.Text.Encoding as Encoding
import Numeric.Natural

import qualified Builtin.Names as Builtin
import Syntax.Annotation
import qualified Syntax.Core as Core
import qualified Syntax.Core.Pattern as Core
import Syntax.GlobalBind
import qualified Syntax.Literal as Core
import qualified Syntax.Pre.Literal as Pre
import Util

inferLit :: Pre.Literal -> (Core.Expr m v, Core.Expr m v)
inferLit (Pre.Integer i) = (Core.Lit $ Core.Integer i, Builtin.IntType)
inferLit (Pre.String s) = (string s, Builtin.StringType)

litPat :: Pre.Literal -> Core.Pat (Core.Expr m v) v'
litPat (Pre.Integer i) = Core.LitPat $ Core.Integer i
litPat (Pre.String s) = stringPat s

string :: Text -> Core.Expr m v
string s
  = Core.App
    (Core.Con Builtin.MkStringConstr)
    Explicit
    (byteArray $ Encoding.encodeUtf8 s)

stringPat :: Text -> Core.Pat (Core.Expr m v) v'
stringPat s
  = Core.ConPat
    Builtin.MkStringConstr
    mempty
    (pure (Explicit, byteArrayPat $ Encoding.encodeUtf8 s, byteArrayType))

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

byteArrayPat :: ByteString -> Core.Pat (Core.Expr m t) b
byteArrayPat bs
  = Core.ConPat Builtin.MkArrayConstr
  (toVector
    [ (Explicit, Builtin.ByteType)
    ])
  (toVector
    [ (Explicit, natPat len, Builtin.Nat)
    , ( Explicit
      , Core.ConPat Builtin.Ref
        (toVector [(Explicit, vecType)])
        (toVector
          [ ( Explicit
            , fst $ ByteString.foldr go (Core.ConPat Builtin.MkUnitConstr mempty mempty, 0) bs
            , vecType
            )
          ]
        )
      , ptrType vecType
      )
    ]
  )
  where
    len = fromIntegral $ ByteString.length bs
    vecType = byteVectorType $ nat len
    go byte (rest, !restLen) =
      ( Core.ConPat Builtin.MkPairConstr
        (toVector
          [ (Explicit, Builtin.ByteType)
          , (Explicit, restType)
          ])
        (toVector
          [ (Explicit, Core.LitPat $ Core.Byte byte, Builtin.ByteType)
          , (Explicit, rest, restType)
          ])
      , restLen + 1
      )
      where
        restType = byteVectorType $ nat restLen

byteArrayType :: Core.Expr m v
byteArrayType = Core.App (global Builtin.ArrayName) Explicit Builtin.ByteType

ptrType :: Core.Expr m v -> Core.Expr m v
ptrType = Core.App (global Builtin.PtrName) Explicit

byteVectorType :: Core.Expr m v -> Core.Expr m v
byteVectorType len = Core.apps
  (global Builtin.VectorName)
  [ (Explicit, len)
  , (Explicit, Builtin.ByteType)
  ]

nat :: Natural -> Core.Expr m v
nat = Core.Lit . Core.Natural

natPat :: Natural -> Core.Pat (Core.Expr m v) v'
natPat = Core.LitPat . Core.Natural
