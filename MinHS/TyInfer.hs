module MinHS.TyInfer where

import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Subst
import MinHS.TCMonad

import Data.Monoid (Monoid (..), (<>))
import Data.Foldable (foldMap)
import Data.List (nub, union, (\\))

primOpType :: Op -> QType
primOpType Gt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ge   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Lt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Le   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Eq   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ne   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Neg  = Ty $ Base Int `Arrow` Base Int
primOpType Fst  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "a"
primOpType Snd  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "b"
primOpType _    = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Int)

constType :: Id -> Maybe QType
constType "True"  = Just $ Ty $ Base Bool
constType "False" = Just $ Ty $ Base Bool
constType "()"    = Just $ Ty $ Base Unit
constType "Pair"  = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "b" `Arrow` (TypeVar "a" `Prod` TypeVar "b"))
constType "Inl"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType "Inr"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "b" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType _       = Nothing

type Gamma = E.Env QType

initialGamma :: Gamma
initialGamma = E.empty

tv :: Type -> [Id]
tv = tv'
 where
   tv' (TypeVar x) = [x]
   tv' (Prod  a b) = tv a `union` tv b
   tv' (Sum   a b) = tv a `union` tv b
   tv' (Arrow a b) = tv a `union` tv b
   tv' (Base c   ) = []

tvQ :: QType -> [Id]
tvQ (Forall x t) = filter (/= x) $ tvQ t
tvQ (Ty t) = tv t

tvGamma :: Gamma -> [Id]
tvGamma = nub . foldMap tvQ

infer :: Program -> Either TypeError Program
infer program = do (p',tau, s) <- runTC $ inferProgram initialGamma program
                   return p'

unquantify :: QType -> TC Type
{-
Normally this implementation would be possible:

unquantify (Ty t) = return t
unquantify (Forall x t) = do x' <- fresh
                             unquantify (substQType (x =:x') t)

However as our "fresh" names are not checked for collisions with names bound in the type
we avoid capture entirely by first replacing each bound
variable with a guaranteed non-colliding variable with a numeric name,
and then substituting those numeric names for our normal fresh variables
-}

unquantify = unquantify' 0 emptySubst
unquantify' :: Int -> Subst -> QType -> TC Type
unquantify' i s (Ty t) = return $ substitute s t
unquantify' i s (Forall x t) = do x' <- fresh
                                  unquantify' (i + 1)
                                              ((show i =: x') <> s)
                                              (substQType (x =:TypeVar (show i)) t)



subUnify :: Type -> Type -> Type -> Type -> TC Subst
subUnify t11 t21 t12 t22 = do
  s <- unify t11 t21
  s' <- unify (substitute s t12) (substitute s t22)
  return (s <> s')


unify :: Type -> Type -> TC Subst
unify (TypeVar v1) (TypeVar v2)
  | v1 == v2 = return emptySubst
  | otherwise = return (v1 =: TypeVar v2)
unify (Base p1) (Base p2)
  | p1 == p2 = return emptySubst    --If p1 /= p2 then nothing is returned
unify (Prod t11 t12) (Prod t21 t22) = subUnify t11 t21 t12 t22
unify (Arrow t11 t12) (Arrow t21 t22) = subUnify t11 t21 t12 t22
unify (Sum t11 t12) (Sum t21 t22) = subUnify t11 t21 t12 t22
unify (TypeVar v) t
  | elem v (tv t) = typeError (OccursCheckFailed v t)  --Use elem to check if v already is in t. elem requires t to be a list, so we must use tv t.
  | otherwise = return (v =: t)
unify t (TypeVar v) = unify (TypeVar v) t
unify t1 t2 = typeError (TypeMismatch t1 t2)



generalise :: Gamma -> Type -> QType
generalise g t = 
  let free = tv t \\ tvGamma g
  in foldr Forall (Ty t) free


inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram g [Bind "main" _ [] prog] = do
  (prog', t, ts) <- inferExp g prog
  let prog'' = allTypes (substQType ts) prog'
  let t' = generalise g t
  return ([Bind "main" (Just t') [] prog''], t, ts)

inferProgram env bs = error "implement me! don't forget to run the result substitution on the"
                            "entire expression using allTypes from Syntax.hs"

inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)
inferExp _ (Num n) = return (Num n, Base Int, emptySubst)

inferExp g (Var x) = case E.lookup g x of 
  Nothing -> typeError (NoSuchVariable x)
  Just t -> do
    t' <- unquantify t 
    return (Var x, t', emptySubst)

inferExp g (Con c) = case constType c of
  Nothing -> typeError (NoSuchConstructor c)
  Just t -> do
    t' <- unquantify t
    return (Con c, t', emptySubst)

inferExp g (Prim op) = do
  t' <- unquantify (primOpType op)
  return (Prim op, t', emptySubst)

inferExp g (App e1 e2) = do
  (e1', t1, ts) <- inferExp g e1
  let substG = substGamma ts g
  (e2', t2, ts') <- inferExp substG e2
  alpha <- fresh
  u <- unify (substitute ts' t1) (Arrow t2 alpha)
  return (App e1' e2', substitute u alpha, u <> ts' <> ts)

inferExp g (If c t e) = do
  (c', t0, ts) <- inferExp g c
  u <- unify t0 (Base Bool)
  let g1 = substGamma (u <> ts) g
  (t', t1, ts1) <- inferExp g1 t
  let g2 = substGamma ts1 g1
  (e', t2, ts2) <- inferExp g2 e
  u' <- unify (substitute ts2 t1) t2
  return (If c' t' e', substitute u' t2, u' <> ts2 <> ts1 <> u <> ts)

inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2]) = do
  (e', t, ts) <- inferExp g e 
  alphaL <- fresh
  let gL = substGamma ts (E.add g (x, Ty alphaL))
  (e1', tl, ts1) <- inferExp gL e1
  alphaR <- fresh
  let gR = substGamma ts1 (E.add gL (y, Ty alphaR))
  (e2', tr, ts2) <- inferExp gR e2
  u <- unify (substitute (ts2 <> ts1 <> ts) (Sum alphaL alphaR)) (substitute (ts2 <> ts1) t)
  u' <- unify (substitute (u <> ts2) tl) (substitute u tr)
  return (
    Case e' [Alt "Inl" [x] e1', Alt "Inr" [y] e2'],
    substitute (u' <> u) tr,
    u' <> u <> ts2 <> ts1 <> ts
    )

inferExp g (Case e _) = typeError MalformedAlternatives

inferExp g (Recfun (Bind fName uType [x] exp)) = do   --Assume 1 argument, might make it more general later
  alpha1 <- fresh
  alpha2 <- fresh
  let g' = E.addAll g ((fName, Ty alpha2) : (x, Ty alpha1) : [])
  (exp', t, ts) <- inferExp g' exp
  u <- unify (substitute ts alpha2) (Arrow (substitute ts alpha1) t)
  let fType = substitute u (Arrow (substitute ts alpha1) t)
  return (Recfun (Bind fName (Just (Ty fType)) [x] exp'), fType, u <> ts)

inferExp g (Let (bind : binds) e2) = do      --Assume only one bind in let-expression
  let Bind lName uType [] e1 = bind
  (e1', t1, ts1) <- inferExp g e1
  let g1 = substGamma ts1 g
  let g2 = E.add g1 (lName, generalise g1 t1)
  (e2', t2, ts2) <- inferExp g2 e2
  let t' = generalise g2 t1
  let bind' = Bind lName (Just t') [] e1'
  return (Let (bind' : binds) e2', t2, ts2 <> ts1)






