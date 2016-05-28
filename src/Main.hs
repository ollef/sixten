{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Monad.Except
import Control.Monad.State
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Foldable
import qualified Data.HashMap.Lazy as HM
import Data.HashSet(HashSet)
import qualified Data.HashSet as HS
import Data.List
import Data.Monoid
import Data.String
import qualified Data.Text.IO as Text
import qualified Data.Vector as V
import Data.Void
import System.Environment

import Builtin
import ClosureConvert
import Erase
import qualified Generate
import Infer
import TCM
import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Concrete as Concrete
import qualified Syntax.Lambda as Lambda
import qualified Syntax.Lifted as Lifted
import qualified Syntax.Parse
import qualified Syntax.Resolve
import Restrict
import TopoSort
import Util

inferProgram :: HashSet Constr -> Program Concrete.Expr Name -> TCM s ()
inferProgram constrs p = mapM_ tcGroup sorted
  where
    deps  = HM.map (bifoldMap defNames toHashSet) p <> HM.fromList constructorMappings
    defNames (DataDefinition d) = toHashSet (constructorNames d) <> toHashSet d
    defNames x = toHashSet x
    sorted = fmap (\n -> (n, bimap (>>>= instCon) (>>= instCon) $ p HM.! n))
           . filter (`HM.member` p) <$> topoSort (HM.toList deps)
    -- TODO check for duplicate constructors
    constructorMappings = [ (c, HS.singleton n)
                          | (n, (DataDefinition d, _)) <- HM.toList p
                          , c <- constructorNames d
                          ]
    constructors = constrs <> HS.fromList (map fst constructorMappings)
    instCon v
      | v `HS.member` constructors = Concrete.Con $ Left v
      | otherwise = pure v

    tcGroup tls = do
      let abstractedScopes = recursiveAbstractDefs [(n, d) | (n, (d, _)) <- tls]
          abstractedTypes = recursiveAbstract [(n, t) | (n, (_, t)) <- tls]
          abstractedTls = [ ( Hint $ Just n
                            , s >>>= unvar (pure . B) Concrete.Global
                            , t >>>= Concrete.Global
                            )
                          | ((s, t), (n, _))
                            <- zip (zip abstractedScopes abstractedTypes) tls]
      checkedTls <- checkRecursiveDefs $ V.fromList abstractedTls

      let vf :: a -> TCM s b
          vf _ = throwError "inferProgram"
      checkedTls' <- traverse (bitraverse (traverse $ traverse vf) (traverse vf)) checkedTls
      let names = V.fromList [n | (n, (_, _)) <- tls]
          instTls = HM.fromList
            [(names V.! i, ( instantiateDef (Abstract.Global . (names V.!)) d
                           , instantiate (Abstract.Global . (names V.!)) t
                           ))
            | (i, (d, t)) <- zip [0..] $ V.toList checkedTls'
            ]
      addContext instTls

test :: FilePath -> IO ()
test inp = do
  mp <- fmap Syntax.Resolve.program <$> Syntax.Parse.parseFromFile Syntax.Parse.program inp
  case mp of
    Nothing         -> return ()
    Just (Left err) -> Text.putStrLn err
    Just (Right p)  -> case runTCM (do
      addContext Builtin.context
      constrs <- HS.fromList . HM.keys <$> gets tcConstrs
      inferProgram constrs p
      cxt <- gets tcContext
      erased <- sequence [(,) x <$> eraseDef e | (x, (e, _)) <- HM.toList cxt]
      restricted <- sequence [(,) x <$> Restrict.restrictBody (Lambda.Sized (Lambda.Lit 1) e) | (x, Definition e) <- erased]
      let liftedRestricted = Restrict.liftProgram restricted
      forM_ liftedRestricted $ \(x, b) -> addArity x $ case b of
        Lifted.FunctionBody (Lifted.Function _ xs _) -> V.length xs
        Lifted.ConstantBody _ -> 0

      converted' <- sequence [(,) x <$> ClosureConvert.convertBody (vacuous e) | (x, e) <- liftedRestricted]
      -- trs "converted'" $ show converted'
      converted <- traverse (traverse (traverse vf)) converted'
      -- trs "converted" $ show converted

      liftedConverted <- traverse (traverse $ traverse va) $ Restrict.liftProgram converted

      qcindex <- qconstructorIndex
      let genv = Generate.GenEnv qcindex (`HM.lookup` lconvprog)
          lconvprog = HM.fromList liftedConverted

      let generated = [(x, fold $ intersperse (fromString "\n") $ snd $ Generate.runGen genv $ Generate.generateBody $ fmap absurd e) | (x, e) <- liftedConverted]

      return (cxt, erased, restricted, converted, generated)
      ) mempty of
      (Left err, t) -> do mapM_ putStrLn t; putStrLn err
      (Right (res, erased, restricted, converted, generated), _) -> do
        mapM_ print $ (\(x, (d, t)) -> runPrettyM $ prettyM x <+> "=" <+> prettyTypedDef (fe d) (fe t) (fst $ pisView $ fe t)) <$> HM.toList res
        putStrLn "------------- erased ------------------"
        mapM_ print $ pretty <$> [(x, fe e) | (x, Definition e) <- erased]
        putStrLn "------------- restricted --------------"
        mapM_ print $ pretty . fmap (fmap show) <$> restricted
        putStrLn "------------- closure-converted --------------"
        mapM_ print $ pretty <$> converted
        putStrLn "------------- generated --------------"
        forM_ generated $ \(n, b) -> do
          Text.putStrLn (n <> fromString " ------------------- ")
          Text.putStrLn b
        -- mapM_ print $ fmap Builder.toLazyText <$> (generated :: [(Name, Builder.Builder)])
  where
    fe :: Functor f => f Void -> f String
    fe = vacuous
    vf :: a -> TCM s String
    vf _ = throwError "inferProgram"
    va :: a -> TCM s b
    va _ = throwError "inferProgram a"

main :: IO ()
main = do
  x:_ <- getArgs
  test x
