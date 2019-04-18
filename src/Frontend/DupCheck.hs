{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Frontend.DupCheck where

import Protolude hiding (TypeError, moduleName)

import Control.Monad.State
import Data.HashMap.Lazy(HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.Text.Prettyprint.Doc as PP
import Text.Parsix.Position

import Driver.Query
import Syntax
import qualified Syntax.Pre.Unscoped as Pre

dupCheck
  :: [(QName, AbsoluteSourceLoc, Pre.Definition)]
  -> Task Query (HashMap QName (SourceLoc, Pre.Definition), [Error])
dupCheck
  = flip runStateT []
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
        modify' (err :)
        return defs
      | otherwise = do
        let
          loc'
            = Relative
            $ RelativeSourceLoc name
            $ spanRelativeTo (spanStart span) span
        return $ HashMap.insert name (loc', def) defs

dupCheckModules
  :: HashMap FilePath ModuleHeader
  -> Task Query (HashMap ModuleName FilePath, [Error])
dupCheckModules
  = flip runStateT []
  . foldM go mempty
  . HashMap.toList
  where
    go modules (file, header)
      | moduleName header `HashMap.member` modules = do
        let
          loc = Syntax.AbsoluteSourceLoc file (Span mempty mempty) Nothing
          prevFile = modules HashMap.! moduleName header
          prevLoc = Syntax.AbsoluteSourceLoc prevFile (Span mempty mempty) Nothing
          prettyModuleName = pretty $ moduleName header
        renderedPrevLoc <- fetchLocationRendering $ Absolute prevLoc
        let
          err = TypeError
            ("Duplicate module " <> red prettyModuleName)
            (Just $ Absolute loc)
            $ PP.vcat
              [ dullBlue prettyModuleName <> " was previously defined at " <> pretty prevLoc
              , renderedPrevLoc
              ]
        modify' (err :)
        return modules
      | otherwise =
        return $ HashMap.insert (moduleName header) file modules
