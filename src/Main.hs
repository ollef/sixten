module Main where

import Control.Monad.Except
import Control.Monad.State
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import qualified Data.HashMap.Lazy as HM
import Data.HashSet(HashSet)
import qualified Data.HashSet as HS
import Data.Monoid
import qualified Data.Text.IO as Text
import qualified Data.Vector as V
import Data.Void
import System.Environment

import Builtin
import ClosureConvert
import Erase
import Infer
import Meta
import TCM
import Syntax
import qualified Syntax.Abstract as Abstract
import qualified Syntax.Concrete as Concrete
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
      restricted <- sequence [(,) x <$> Restrict.restrictExpr e | (x, Definition e) <- erased]
      let liftedRestricted = Restrict.liftProgram restricted
      forM_ liftedRestricted $ \(x, b) -> addArity x $ case b of
        Lifted.Function xs _ -> V.length xs
        Lifted.Constant _ -> 0

      converted' <- sequence [(,) x <$> ClosureConvert.convertBody (vacuous e) | (x, e) <- liftedRestricted]
      trs "converted'" $ show converted'
      converted <- traverse (traverse (traverse vf)) converted'
      trs "converted" $ show converted

      return (cxt, erased, restricted, converted)
      ) mempty of
      (Left err, t) -> do mapM_ putStrLn t; putStrLn err
      (Right (res, erased, restricted, converted), _) -> do
        mapM_ print $ (\(x, (d, t)) -> runPrettyM $ prettyM x <+> prettyM "=" <+> prettyTypedDef (fe d) (fe t) (fst $ bindingsView piView $ fe t)) <$> HM.toList res
        putStrLn "------------- erased ------------------"
        mapM_ print $ pretty <$> [(x, fe e) | (x, Definition e) <- erased]
        putStrLn "------------- restricted --------------"
        mapM_ print $ pretty . fmap (fmap show) <$> restricted
        putStrLn "------------- closure-converted --------------"
        mapM_ print $ pretty <$> converted
  where
    fe :: Functor f => f Void -> f String
    fe = vacuous
    vf :: a -> TCM s String
    vf _ = error "inferProgram"

main :: IO ()
main = do
  x:_ <- getArgs
  test x
