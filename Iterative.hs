import Control.Monad
import Data.Maybe
import qualified Data.Map as M
import Debug.Trace


sToA :: Strict -> Applicative
sToA S = C
sToA L = Q

lub :: Strict -> Applicative -> Applicative
lub L _ = Q
lub S a = a

-- NB: anything not in the mapping is implicitly (L, Q)
-- Luckily, (L, Q) `both` (s, a) == (s, a), so we can
-- just take the union and leave the extra elements alone
bothFVs :: M.Map Var (IType, (Strict, Applicative))
        -> M.Map Var (IType, (Strict, Applicative))
        -> M.Map Var (IType, (Strict, Applicative))
bothFVs = M.unionWith (\(i1, (s1, a1)) (i2, (s2, a2)) -> (bothI i1 i2, (s1 `bothS` s2, a1 `bothA` a2)))
  where
    bothS L s = s
    bothS s L = s
    bothS S S = S

    bothA Q a = a
    bothA a Q = a
    bothA C C = C

    bothI IBaseTy            IBaseTy
      = IBaseTy
    bothI (IFunTy ty1 a1 i1) (IFunTy ty2 a2 i2)
      | a1 == a2
      = IFunTy ty1 a1 (i1 `bothI` i2) -- NB: ty1 == ty2 or we have a type mismatch
      | otherwise
      = error $ "I don't know what to do here!\n" ++ show (IFunTy ty1 a1 i1) ++ "\n" ++ show (IFunTy ty2 a2 i2)


data Type = BaseTy | FunTy Type Type
          deriving (Eq)

infixr 9 `FunTy`

instance Show Type where
    show BaseTy = "?"
    show (FunTy t1 t2) = "(" ++ show t1 ++ ") -> " ++ show t2

data Strict = S -- Strict
            | L -- Lazy
            deriving (Eq, Show)

data Applicative = Q -- seQ
                 | C -- Call
                 deriving (Eq, Show)

-- Information about the demand placed on a term: is the *result* of a function
-- actually applied to further, or is it just seqed?
data IType = IBaseTy | IFunTy OType Applicative IType
           deriving (Eq)

instance Show IType where
    show IBaseTy = "?"
    show (IFunTy t1 a2 i2)  = "(" ++ show t1 ++ ") -> (" ++ show i2 ++ ")" ++ show a2

-- Information about the demand it is safe for a term to exert: may the *argument* of a
-- function be evaluated strictly, and if it may be, can it be applied to or just seqed?
--
-- Also records the demand that may safely be placed on calling functional arguments to the term.
data OType = OBaseTy | OFunTy Applicative IType Strict OType
           deriving (Eq)

{-
-- NB: unlike OType, IType gives you no information you can use to build a wrapper
wrapper :: OType -> Term -> Term
wrapper OBaseTy             e = e
wrapper (OFunTy _a i1 s o2) e = Lam f (Lam x (wrapper o2 (Var f `app` Var x))) `SApp` e
  where f = V "f" (termType e)
        x = V "x" (iToT i1)

        iToT IBaseTy          = BaseTy
        iToT (IFunTy t1 a i2) = FunTy t1 (iToT i2)

        app = case s of L -> App; S -> SApp
-}

instance Show OType where
    show OBaseTy = "?"
    show (OFunTy a1 o1 s o2) = "(" ++ show o1 ++ ")" ++ show a1 ++ " -{" ++ show s ++ "}> " ++ show o2

tToI :: Type -> IType
tToI BaseTy = IBaseTy
tToI (FunTy t1 t2) = IFunTy (tToO t1) Q (tToI t2)

iToO :: IType -> OType
iToO IBaseTy            = OBaseTy
iToO (IFunTy t1 _a2 i2) = OFunTy Q (oToI t1) L (iToO i2)

tToO :: Type -> OType
tToO = iToO . tToI

oToI :: OType -> IType
oToI OBaseTy               = IBaseTy
oToI (OFunTy _a1 i1 _s o2) = IFunTy (iToO i1) Q (oToI o2)

{-
activate :: IType -> OType -> OType
activate IBaseTy           OBaseTy             = OBaseTy
activate (IFunTy t1 a2 i2) (OFunTy a1 i1 s o2) = OFunTy (a1 )
-}


data Var = V { varName :: String, varType :: Type }
         deriving (Show)

instance Eq Var where
    V s1 _ == V s2 _ = s1 == s2

instance Ord Var where
    V s1 _ `compare` V s2 _ = s1 `compare` s2


data Term = Var Var | Lam Var Term | App Term Term | SApp Term Term

infixl 9 `App`

instance Show Term where
    show (Var x) = varName x
    show (Lam x e) = "\\" ++ varName x ++ ". " ++ show e
    show (App e1 e2) = "(" ++ show e1 ++ ") (" ++ show e2 ++ ")"
    show (SApp e1 e2) = "(" ++ show e1 ++ ") $! (" ++ show e2 ++ ")"


termType :: Term -> Type
termType (Var x) = varType x
termType (Lam x e) = FunTy (varType x) (termType e)
termType (App e1 _) = case termType e1 of FunTy _ t2 -> t2
termType (SApp e1 _) = case termType e1 of FunTy _ t2 -> t2

contain :: Applicative -> M.Map Var (IType, (Strict, Applicative)) -> M.Map Var (IType, (Strict, Applicative))
contain C fvs = fvs
contain Q fvs = M.map (\(i, _) -> (i, (L, Q))) fvs

infer, infer' :: M.Map Var OType -> Term -> (IType, (Strict, Applicative)) -> (Term, M.Map Var (IType, (Strict, Applicative)), OType)
infer = infer'
--infer e (i, (s, a)) = trace ("infer " ++ show (e, i, (s, a)) ++ "\n == " ++ show (e', fvs, o)) $ (e', fvs, o)
--  where (e', fvs, o) = infer' e (i, (s, a))

infer' env (Var x)   (i, (s, a)) = (Var x, M.singleton x (i, (s, a)), fromMaybe (tToO (varType x)) (M.lookup x env))
infer' env (Lam x e) (IFunTy o1 a_body i2, (_s, a)) = (Lam x e', contain a (M.delete x fvs2), OFunTy a1 i1 s1 o2)
  where (e', fvs2, o2) = infer (M.insert x o1 env) e (i2, (S, a_body))
        (i1, (s1, a1)) = fromMaybe (tToI (varType x), (L, Q)) (M.lookup x fvs2)
infer' env (App e1 e2) (i, (s, a)) = go (tToO (termType e2))
  where
    go o1 | o1 == o1' = (e1' `app` e2', bothFVs fvs1 fvs2, o2)
          | otherwise = go o1'
      where (e1', fvs1, OFunTy a1 i1 s1 o2) = infer env e1 (IFunTy o1 a i, (s, sToA s))
            (s2, app) = case s1 of
              L -> (L, App)
              S -> (s, SApp)
            (e2', fvs2, o1') = infer env e2 (i1, (s2, s `lub` a1))
infer' _ (SApp _ _) _ = error "Don't handle strict applications in input"


e_test1, e_test2, e_test3 :: Term

-- (x b) ((\y -> b) (x b))
--  ==>
-- (x b) ((\y -> b) (x b))
-- {x |-> (?Q -L> ?Q -L> ?)}
e_test1 = (Var x `App` Var b) `App` ((Lam y (Var b)) `App` (Var x `App` Var b))
  where
    x = V "x" (BaseTy `FunTy` BaseTy `FunTy` BaseTy)
    y = V "y" (BaseTy `FunTy` BaseTy)
    b = V "b" BaseTy

-- (\x y -> x) b b
--  ==>
-- (\x y -> x) !b b
e_test2 = Lam x (Lam y (Var x)) `App` Var b `App` Var b
  where
    x = V "x" BaseTy
    y = V "y" BaseTy
    b = V "b" BaseTy

-- (\f -> f b b) (\x y -> x)
--  ==>
-- (\f -> f !b b) (\x y -> x)
e_test3 = Lam f (Var f `App` Var b `App` Var b) `App` (Lam x (Lam y (Var x)))
  where
    x = V "x" BaseTy
    y = V "y" BaseTy
    b = V "b" BaseTy
    f = V "f" (BaseTy `FunTy` BaseTy `FunTy` BaseTy)

main :: IO ()
main = forM_ [e_test3, e_test2, e_test1] $ \e_test -> print $ infer M.empty e_test (IBaseTy, (S, Q))
