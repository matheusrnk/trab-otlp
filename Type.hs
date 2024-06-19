module Type where
import Data.List(nub, intersect, union)

type Index  = Int
type Id     = String
data TI a   = TI (Index -> (a, Index))
type Subst  = [(Id, SimpleType)]
data Assump = Id :>: SimpleType deriving (Eq, Show)

data SimpleType  =  TVar Id
                  | TArr SimpleType SimpleType
                  | TCon String -- todo
                  -- | TApp SimpleType SimpleType -- todo
                  | TGen Int -- todo
                  deriving Eq

instance Show SimpleType where -- serve para melhorar o print
   show (TVar i)    = i
   show (TArr (TVar i) t) = i ++ " -> " ++ show t
   show (TArr (TCon s) t) = s ++ " -> " ++ show t
   show (TArr (TGen n) t) = "Gen" ++ show n ++ " -> " ++ show t
   show (TArr t t')       = "(" ++ show t ++ ") -> " ++ show t'
   show (TCon s)          = s
   --show (TApp t1 t2)      = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
   show (TGen n)          = "Gen" ++ show n

--------------------------
 -- compõem o monada que faz a propagação
instance Functor TI where
   fmap f (TI m) = TI (\e -> let (a, e') = m e in (f a, e'))

instance Applicative TI where
   pure a = TI (\e -> (a, e))
   TI fs <*> TI vs = TI (\e -> let (f, e') = fs e; (a, e'') = vs e' in (f a, e''))

instance Monad TI where
   return x = TI (\e -> (x, e))
   TI m >>= f  = TI (\e -> let (a, e') = m e; TI fa = f a in fa e')
--------------------------

freshVar :: TI SimpleType
freshVar = TI (\e -> let v = "t"++show e in (TVar v, e+1)) -- cria um nova variavel de tipo

runTI (TI m) = let (t, _) = m 0 in t -- monada que faz a propagação propriamente dita
                                     -- m = (SimpleType, Subst)
                                     -- TI m = TI (SimpleType, Subst) = (tiExpr iniCont e) -- É oq esta funcao retorna
----------------------------

t --> t' = TArr t t' -- apenas uma representação do construtor TArr

infixr 4 @@
(@@)       :: Subst -> Subst -> Subst -- compositor de substituições (ou combinador)
s1 @@ s2    = [ (u, apply s1 t) | (u,t) <- s2 ] ++ s1

dom = map (\(i:>:_)->i) -- retorna o nome de todos no contexto

-- basicamente é um operador de união de contextos
as /+/ as' = as' ++ filter compl as -- filtra em as aqueles que não estao no contexto de as'
   where
     is = dom as'
     compl (i:>:_) = notElem i is -- verifica se i está no contexto as'
---------------------------- 

class Subs t where
  apply :: Subst -> t -> t -- aplica uma substituição
  tv    :: t -> [Id] -- nomes no contexto?

instance Subs SimpleType where -- subtituicao em tipo
  apply s (TVar u)  =
                    case lookup u s of -- se a variavel estiver na substituicao...
                       Just t  -> t -- retorna o seu mapeamento associado
                       Nothing -> TVar u -- senão, não tem e fica não-modificado
  apply s (TArr l r) =  TArr (apply s l) (apply s r)
  apply s (TCon u) = 
                    case lookup u s of
                       Just t  -> t
                       Nothing -> TCon u
  --apply s (TApp l r) = TApp (apply s l) (apply s r)
  apply s (TGen i) = case lookup ("Gen" ++ show i) s of
                       Just t -> t
                       Nothing -> TGen i
  

  tv (TVar u)  = [u]
  tv (TArr l r) = tv l `union` tv r
  tv (TCon u) = [u]
  --tv (TApp l r) = tv l `union` tv r
  tv (TGen i) = ["Gen" ++ show i]


instance Subs a => Subs [a] where
  apply s     = map (apply s)
  tv          = nub . concat . map tv

instance Subs Assump where -- substituicao em contexto
  apply s (i:>:t) = i:>:apply s t
  tv (i:>:t) = tv t -- retona o nome de todos os tipos.

------------------------------------
-- instantiate :: será uma funcao que substituirá os 
-- quantificadores gerais por monotipos
-- Exemplo: Va Vb. a -> b
--          t0 -> t1

varBind :: Id -> SimpleType -> Maybe Subst
varBind u t | t == TVar u   = Just []
            | u `elem` tv t = Nothing -- verifica recursividade
            | otherwise     = Just [(u, t)]

conBind :: Id -> SimpleType -> Maybe Subst
conBind u t | t == TCon u = Just []
            | otherwise   = Nothing -- pq nao tem como unificar, por exemplo "int ~ bool"


-- tenta fazer a unificação propriamente
-- most general unifier
mgu (TArr l r,  TArr l' r') = do s1 <- mgu (l,l')
                                 s2 <- mgu ((apply s1 r) ,  (apply s1 r'))
                                 return (s2 @@ s1)
mgu (t,        TVar u   )   =  varBind u t
mgu (TVar u,   t        )   =  varBind u t
mgu (t,        TCon u   )   =  conBind u t
mgu (TCon u,   t        )   =  conBind u t

unify t t' =  case mgu (t,t') of
    Nothing -> error ("\ntrying to unify:\n" ++ (show t) ++ "\nand\n" ++
                      (show t')++"\n")
    Just s  -> s

