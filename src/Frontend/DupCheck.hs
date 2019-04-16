{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Frontend.DupCheck where

import Protolude hiding (TypeError)

import Control.Monad.State
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.Text.Prettyprint.Doc as PP
import Text.Parsix.Position

import Driver.Query
import Syntax
import qualified Syntax.Pre.Unscoped as Pre

data DupState = DupState
  { instanceNumber :: !Int
  , errors :: [Error]
  }

dupCheck
  :: [(QName, AbsoluteSourceLoc, Pre.Definition)]
  -> Task Query (HashMap QName (SourceLoc, Pre.Definition), [Error])
dupCheck
  = fmap (second errors)
  . flip runStateT (DupState 0 [])
  . foldM go mempty
  where
    go defs (name, loc@(Syntax.AbsoluteSourceLoc _ span _), def)
      | name `HashMap.member` defs = do
        let
          (prevLoc, _) = defs HashMap.! name
        aprevLoc <- fetchAbsoluteSourceLoc prevLoc
        renderedPrevLoc <- fetchLocationRendering prevLoc
        let
          err = TypeError
            "Duplicate definition"
            (Just $ Absolute loc)
            $ PP.vcat
              [ "Previous definition at " <> pretty aprevLoc
              , renderedPrevLoc
              ]
        modify' $ \s -> s { errors = err : errors s }
        return defs
      | otherwise = do
        let
          loc'
            = Relative
            $ RelativeSourceLoc name
            $ spanRelativeTo (spanStart span) span
        return $ HashMap.insert name (loc', def) defs
