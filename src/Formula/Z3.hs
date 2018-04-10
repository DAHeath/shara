{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TemplateHaskell #-}
module Formula.Z3 where

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Except

import           Data.List (partition)
import           Data.Maybe
import qualified Data.Map as M
import           Data.Map (Map)

import           Formula (Expr((:@)), Chc, Type((:=>)), Var(..))
import qualified Formula as F

import           Z3.Monad hiding (local)

data Env = Env { _envVars :: Map Var AST
               , _envFuns :: Map Var FuncDecl
               } deriving (Show, Eq, Ord)
makeLenses ''Env

type SMT n m = (MonadState Env m, MonadZ3 m)

interpolate :: MonadIO m => Expr -> Expr -> m (Either (Map Var Expr) Expr)
interpolate e e' = runEnvZ3 $ do
  f  <- formToAst e
  f' <- mkInterpolant =<< formToAst e'
  t <- mkInterpolant =<< mkAnd [f, f']
  is <- computeInterpolant t =<< mkParams
  case is of
    Just (Right (i:_)) -> Right <$> astToExpr i
    Just (Left m) -> Left <$> modelToModel m
    _ -> error "invalid return from 'interpolate'"

-- | Invoke `duality` to solve the relational post fixed-point problem.
solveChc :: (MonadError F.Model m, MonadIO m) => [Chc] -> m F.Model
solveChc hcs = do
  res <- runEnvZ3 sc
  case res of
    Left e -> throwError e
    Right m -> return m
  where
    sc = do
      let (queries, rules) = partition F.isQuery hcs
      let qids = map (const "x0/q") queries
      let qs = zipWith mkQuery queries qids
      let satForms = map F.chcExpr rules ++ qs
      let rids = map (\n -> "RULE" ++ show n) [0..length hcs-1]
      useDuality
      forms <- traverse formToAst satForms
      rids' <- traverse mkStringSymbol rids
      zipWithM_ fixedpointAddRule forms rids'

      let quers = [Var "x" F.Bool]
      quers' <- traverse funcToDecl quers
      res <- fixedpointQueryRelations quers'
      case res of
        Unsat -> Right <$> (modelToModel =<< fixedpointGetModel)
        _     -> Left <$> (modelToModel =<< fixedpointGetRefutation)

    mkQuery q n =
      let theQuery = F.V $ F.Var n F.Bool in
      F.app2 F.Impl (F.mkNot $ F.chcExpr q) theQuery

    useDuality = do
      pars <- mkParams
      join $ paramsSetSymbol pars <$> mkStringSymbol "engine" <*> mkStringSymbol "duality"
      fixedpointSetParams pars

-- | Find a satisfying model of an input formula (if one exists).
satisfy :: MonadIO m => Expr -> m (Maybe F.Model)
satisfy f = runEnvZ3 $ do
  assert =<< formToAst f
  (_, m) <- solverCheckAndGetModel
  case m of
    Nothing -> return Nothing
    Just m' -> Just <$> modelToModel m'

-- | The the satisfiability of the input formula.
isSat :: MonadIO m => Expr -> m Bool
isSat f = do
  sol <- runEnvZ3 sc
  case sol of
    Sat -> return True
    _   -> return False
  where sc = (assert =<< formToAst f) >> check

-- | Test the validity of the input formula.
isValid :: MonadIO m => Expr -> m Bool
isValid f = runEnvZ3 $ do
  sol <- sc
  case sol of
    Unsat -> return True
    _     -> return False
  where sc = (assert =<< formToAst (F.mkNot f)) >> check

forallIsSat :: MonadIO m => Expr -> m Bool
forallIsSat e = do
  sol <- runEnvZ3 ((assert =<< e') >> check)
  case sol of
    Sat -> return True
    _ -> return False
  where
    vs = e ^.. F.vars
    e' = do
      vs' <- mapM (\v -> do
        v' <- varDec v
        toApp =<< mkApp v' []) vs
      mkForallConst [] vs' =<< formToAst e

-- | Is `f -> g` a valid formula?
entails :: MonadIO m => Expr -> Expr -> m Bool
entails f g = isValid (F.app2 F.Impl f g)

simplify :: MonadIO m => Expr -> m Expr
simplify f = runEnvZ3 $ astToExpr =<< Z3.Monad.simplify =<< formToAst f

superSimplify :: MonadIO m => Expr -> m Expr
superSimplify (F.LInt n) = return (F.LInt n)
superSimplify f = runEnvZ3 $ astToExpr =<< superSimp =<< formToAst f
  where
    superSimp :: MonadZ3 m => AST -> m AST
    superSimp ast = do
      tac  <- join $ andThenTactic <$> mkTactic "propagate-values" <*> skipTactic
      tac' <- join $ andThenTactic <$> mkTactic "ctx-solver-simplify" <*> pure tac

      g <- mkGoal False False False
      goalAssert g ast
      rs <- getApplyResultSubgoals =<< applyTactic tac' g
      asts <- concat <$> mapM getGoalFormulas rs
      case asts of
        (f' : _) -> return f'
        _ -> return ast

-- | A monadic context for Z3 actions which caches the variables and functions
-- which have already been created. It also resolve DeBrujin indices which Z3
-- uses to represent variables.
newtype EnvZ3 n a = EnvZ3 { getEnvZ3 :: StateT Env Z3 a }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadState Env
           , MonadIO
           )

instance MonadZ3 (EnvZ3 n) where
  getSolver     = EnvZ3 $ lift getSolver
  getContext    = EnvZ3 $ lift getContext
  getFixedpoint = EnvZ3 $ lift getFixedpoint

runEnvZ3 :: MonadIO m => EnvZ3 n a -> m a
runEnvZ3 ac = liftIO $ evalZ3 (evalStateT (getEnvZ3 ac') emptyEnv)
  where
    ac' = push *> ac <* reset
    emptyEnv = Env M.empty M.empty

-- | Convert the ADT formula to a Z3 formula.
formToAst :: SMT n m => Expr -> m AST
formToAst f =
  case f of
    F.V v               -> var v
    F.LUnit             -> undefined
    F.LBool True        -> mkTrue
    F.LBool False       -> mkFalse
    F.LInt l            -> mkInteger l
    f' :@ a             -> let (f'', as) = gatherApp f' [a]
                           in appToZ3 f'' as
    _ -> undefined
  where
    gatherApp :: Expr -> [Expr] -> (Expr, [Expr])
    gatherApp (f' :@ a) args = gatherApp f' (a : args)
    gatherApp x args = (x, args)

    register v = do
      fd <- varDec v
      -- fixedpointRegisterVariable fd
      v' <- mkApp fd []
      envVars %= M.insert v v'
      return v'

    var v = do
      env <- use envVars
      case M.lookup v env of
        Nothing -> register v
        Just v' -> return v'

-- | Convert a function application to a Z3 formula.
appToZ3 :: SMT n m => Expr -> [Expr] -> m AST
appToZ3 f args =
  case f of
    F.V v        -> join $ mkApp <$> funcToDecl v <*> traverse formToAst args
    F.Not        -> mkNot =<< formToAst (head args)
    F.And        -> many mkAnd
    F.Or         -> many mkOr
    F.Add _      -> many mkAdd
    F.Mul _      -> many mkMul
    F.Sub _      -> many mkSub
    F.Distinct _ -> many mkDistinct
    F.Impl       -> two mkImplies
    F.Iff        -> two mkIff
    F.Div _      -> two mkDiv
    F.Mod _      -> two mkRem
    F.If _       -> three mkIte

    F.Eql _      -> two mkEq
    F.Nql t      -> mkNot =<< appToZ3 (F.Eql t) args
    F.Lt _       -> two mkLt
    F.Le _       -> two mkLe
    F.Gt _       -> two mkGt
    F.Ge _       -> two mkGe

    F.LUnit      -> undefined
    F.LBool b    -> mkBool b
    F.LInt _     -> undefined
    _ :@ _       -> undefined

  where
    many o = o =<< traverse formToAst args
    two o = join $ o <$> formToAst (head args) <*> formToAst (args !! 1)
    three o = join $ o <$> formToAst (head args)
                       <*> formToAst (args !! 1)
                       <*> formToAst (args !! 2)

formFromApp :: MonadZ3 z3 => String -> [AST] -> Sort -> z3 Expr
formFromApp n args range
  | n == "true"  = return $ F.LBool True
  | n == "false" = return $ F.LBool False
  -- The 'app' is just a variable
  | null args = do
    typ <- sortToType range
    return $ F.V $ F.Var n typ
  | n == "ite" || n == "if" = do
    c <- astToExpr (head args)
    e1 <- astToExpr (args !! 1)
    e2 <- astToExpr (args !! 2)
    return $ F.appMany (F.If (F.exprType e1)) [c, e1, e2]
  | n == "and"      = F.manyAnd  <$> traverse astToExpr args
  | n == "or"       = F.manyOr   <$> traverse astToExpr args
  | n == "+"        = F.manyIAdd <$> traverse astToExpr args
  | n == "*"        = F.manyIMul <$> traverse astToExpr args
  | n == "mod"      = liftMany (F.Mod F.Int)
  | n == "rem"      = liftMany (F.Mod F.Int)
  | n == "distinct" = liftMany (F.Distinct F.Int)
  | n == "div"      = lift2 (F.Div F.Int)
  | n == "iff"      = lift2 F.Iff
  | n == "=>"       = lift2 F.Impl
  | n == "<"        = lift2 (F.Lt F.Int)
  | n == "<="       = lift2 (F.Le F.Int)
  | n == ">"        = lift2 (F.Gt F.Int)
  | n == ">="       = lift2 (F.Ge F.Int)
  | n == "="        = F.mkEql F.Int <$> astToExpr (head args) <*> astToExpr (args !! 1)
  | n == "not"      = F.mkNot <$> astToExpr (head args)
  | n == "-"        = if length args == 1
                         then F.app2 (F.Sub F.Int) (F.LInt 0) <$> astToExpr (head args)
                         else lift2 (F.Sub F.Int)
  | otherwise = do
    -- Found a function that is as of yet unknown.
    liftIO $ putStrLn ("applying: " ++ n)
    args' <- traverse astToExpr args
    domain <- traverse getType args
    range' <- sortToType range
    let f = F.Var n (F.curryType domain range')
    return $ F.appMany (F.V f) args'
  where lift2 f = F.app2 f <$> astToExpr (head args) <*> astToExpr (args !! 1)
        liftMany f = F.appMany f <$> traverse astToExpr args

-- | Convert a Z3 model to the AST-based formula model.
modelToModel :: (MonadState Env z3, MonadZ3 z3)
             => Model -> z3 F.Model
modelToModel m = traverse superSimplify =<< M.union <$> functions <*> constants
  where
    functions = do
      fds <- modelGetFuncDecls m
      fds' <- traverse declToFunc fds
      fi <- catMaybes <$> traverse (modelGetFuncInterp m) fds
      fe <- traverse (astToExpr <=< funcInterpGetElse) fi
      return $ M.fromList $ zip fds' fe

    constants = do
      fds <- modelGetConstDecls m
      vs <- traverse declToFunc fds
      fi <- catMaybes <$> traverse (modelGetConstInterp m) fds
      fe <- traverse astToExpr fi
      return $ M.fromList $ zip vs fe

    declToFunc fd = do
      n <- declName fd
      domain <- traverse sortToType =<< getDomain fd
      range  <- sortToType =<< getRange fd
      if n == "@Fail!0"
      then return $ F.Var "x0/Fail" (F.curryType domain range)
      else return $ F.Var n (F.curryType domain range)

-- | Convert the Z3 internal representation of a formula to the AST representation.
astToExpr :: MonadZ3 z3 => AST -> z3 Expr
astToExpr arg = do
  k <- getAstKind arg
  case k of
    Z3_NUMERAL_AST ->
      do t <- getType arg
         rep <- getNumeralString arg
         case t of
           F.Int  -> return $ F.LInt  $ read rep
           _       -> error "unknown numeric type"

    Z3_APP_AST ->
      do app <- toApp arg
         decl <- getAppDecl app
         n <- declName decl
         args <- getAppArgs app
         range <- getRange decl
         formFromApp n args range

    Z3_VAR_AST -> F.V <$> (F.bound <$> (toInteger <$> getIndexValue arg) <*> getType arg)

    Z3_QUANTIFIER_AST -> do liftIO $ putStrLn "quantifier!"
                            undefined

    Z3_SORT_AST -> do liftIO $ putStrLn "sort!"
                      undefined

    Z3_FUNC_DECL_AST -> do liftIO $ putStrLn "func decl!"
                           undefined

    Z3_UNKNOWN_AST -> do liftIO $ putStrLn "unknown!"
                         undefined

typeToSort :: MonadZ3 z3 => Type -> z3 Sort
typeToSort = \case
  F.Unit       -> mkIntSort
  F.Bool       -> mkBoolSort
  F.Int        -> mkIntSort
  _ :=> _      -> undefined
  F.List _     -> undefined

sortToType :: MonadZ3 z3 => Sort -> z3 Type
sortToType s = do
  sk <- getSortKind s
  case sk of
    Z3_UNINTERPRETED_SORT  -> error "unsupported sort kind"
    Z3_BOOL_SORT           -> return F.Bool
    Z3_INT_SORT            -> return F.Int
    Z3_REAL_SORT           -> error "unsupported sort kind"
    Z3_BV_SORT             -> error "unsupported sort kind"
    Z3_ARRAY_SORT          -> error "unsupported sort kind"
    Z3_DATATYPE_SORT       -> error "unsupported sort kind"
    Z3_RELATION_SORT       -> error "unsupported sort kind"
    Z3_FINITE_DOMAIN_SORT  -> error "unsupported sort kind"
    Z3_FLOATING_POINT_SORT -> error "unsupported sort kind"
    Z3_ROUNDING_MODE_SORT  -> error "unsupported sort kind"
    Z3_UNKNOWN_SORT        -> error "unsupported sort kind"

getType :: MonadZ3 z3 => AST -> z3 Type
getType = getSort >=> sortToType

declName :: MonadZ3 z3 => FuncDecl -> z3 String
declName = getDeclName >=> getSymbolString

funcToDecl :: (MonadState Env z3, MonadZ3 z3) => Var -> z3 FuncDecl
funcToDecl r = do
  let t = r ^. F.varType
  let n = r ^. F.varName
  env <- use envFuns
  case M.lookup r env of
    Nothing -> do
      sorts <- traverse typeToSort (F.domain t)
      sym <- mkStringSymbol n
      r' <- mkFuncDecl sym sorts =<< typeToSort (F.range t)
      fixedpointRegisterRelation r'
      envFuns %= M.insert r r'
      return r'
    Just r' -> return r'

varDec :: MonadZ3 z3 => Var -> z3 FuncDecl
varDec v = do
  let t = v ^. F.varType
  let n = v ^. F.varName
  sym <- mkStringSymbol n
  mkFuncDecl sym [] =<< typeToSort t
