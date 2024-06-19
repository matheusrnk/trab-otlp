import Text.Parsec
import qualified Text.Parsec.Token as L
import Text.Parsec.Language (emptyDef)
import Type
import Data.Char (isLower)
import Data.List (nub)
import Control.Monad.Identity

data Pat = PVar Id
           | PLit Literal
           | PCon Id [Pat]
           deriving (Eq, Show)

data Literal = LitInt Integer | LitBool Bool deriving (Show, Eq)

data Expr = Var Id
            | Const Id
            | App Expr Expr
            | Lam Id Expr
            | Lit Literal
            | If Expr Expr Expr
            | Case Expr [(Pat, Expr)]
            | Let (Id, Expr) Expr
            deriving (Eq, Show)

-- funcs utilizadas do Type.hs => freshVar, /+/, apply, -->, @@, unify

tiContext :: [Assump] -> Id -> TI SimpleType
tiContext g i = if l /= [] then inst t else error ("Undefined: " ++ i ++ "\n")
   where
      l = dropWhile (\(i' :>: _) -> i /= i' ) g
      (_ :>: t) = head l

findQuantifiers :: SimpleType -> [SimpleType]
findQuantifiers (TVar u)   = []
findQuantifiers (TArr l r) = findQuantifiers l ++ findQuantifiers r
findQuantifiers (TCon u)   = []
findQuantifiers (TGen u)   = [TGen u]

mapTGensToFreshVars :: [SimpleType] -> TI Subst
mapTGensToFreshVars tgens = do
    mapM createFreshVarSubst tgens
  where
    createFreshVarSubst :: SimpleType -> TI (Id, SimpleType)
    createFreshVarSubst (TGen n) = do
        b <- freshVar
        return ("Gen" ++ show n, b)
    createFreshVarSubst _ = error "Expected a TGen"

inst :: SimpleType -> TI SimpleType
inst t = do
            let x = nub $ findQuantifiers t
            if x /= [] then
                do
                  s <- mapTGensToFreshVars x
                  return $ apply s t
            else
                return t

tiExpr :: [Assump] -> Expr -> TI (SimpleType, Subst)
tiExpr g (Var i) = do {t <- tiContext g i; return (t, [])}
tiExpr g (App e e') = do (t, s1) <- tiExpr g e
                         (t', s2) <- tiExpr (apply s1 g) e'
                         b <- freshVar
                         let s3 = unify (apply s2 t) (t' --> b)
                         return (apply s3 b, s3 @@ s2 @@ s1)
tiExpr g (Lam i e) = do b <- freshVar
                        (t, s)  <- tiExpr (g/+/[i:>:b]) e
                        return (apply s (b --> t), s)
tiExpr g (Const i) = do {t <- tiContext g i; return (t, [])}
tiExpr g (Lit (LitBool b)) = do {t <- tiContext g (show b); return (t, [])}
tiExpr g (Lit (LitInt i)) = return (TCon "Int", [])
-- tiExpr g (If e e' e'') = todo
-- tiExpr g (Case e ((p, e'):patts)) = todo
-- tiExpr g (Let (i, e) e') = todo

--- Examples ---
ex1 = Lam "f" (Lam "x" (App (Var "f") (Var "x")))
ex2 = Lam "x" (App (Var "x") (Var "x"))
ex3 = Lam "g" (Lam "f" (Lam "x" (App (Var "g") (App (Var "f") (Var "x")))))
ex4 = Lam "x" (Lam "x" (Var "x"))
ex5 = Lam "w" (Lam "y" (Lam "x" (App (Var "y") (App (App (Var "w") (Var "y")) (Var "x")))))
ex6 = Lam "x" (Lam "y" (Lam "w" (Lam "u" (App (App (Var "x") (Var "w")) (App (App (Var "y") (Var "w")) (Var "u"))))))

-- (,) : t0 -> (t1 -> (("(,)" t0) t1))  => t0 -> t1 -> (t0, t1)
--iniCont = ["(,)" :>: TArr (TGen 0) (TArr (TGen 1) (TApp (TApp (TCon "(,)") (TGen 0)) (TGen 1))),
--            "True" :>: TCon "Bool", "False" :>: TCon "Bool"]
iniCont = ["(,)" :>: TArr (TGen 0) (TArr (TGen 1) (TArr (TArr (TCon "(,)") (TGen 0)) (TGen 1))),
            "True" :>: TCon "Bool", "False" :>: TCon "Bool"]


infer e = runTI (tiExpr iniCont e) -- passa o contexto inicial

-------- Lexical ---------------

lingDef = emptyDef
          { L.commentStart = "{-"
           ,L.commentEnd   = "-}"
           ,L.commentLine  = "--"
           ,L.identStart   = letter
           ,L.identLetter  = letter
           ,L.reservedNames = ["let", "in", "if", "then", "else", "True", "False", "case", "of"]
           ,L.reservedOpNames = [".", "=", "->"]
          }

lexical = L.makeTokenParser lingDef

recInteger = L.integer lexical
symbol     = L.symbol lexical
parens     = L.parens lexical
braces     = L.braces lexical
identifier = L.identifier lexical
reserved   = L.reserved lexical
reservedOp = L.reservedOp lexical

--------- Parser -----------------
parseExpr = runParser expr [] "lambda-calculus"

expr :: Parsec String u Expr
expr = chainl1 parseNonApp $ return $ App

var i = do {return (Var i)}

cons i = do {return (Const i)}

varOrCons = do
    i <- identifier
    if isLower (head i) then var i
    else cons i

litInteger = do {LitInt <$> recInteger;}

litBool = do {reserved "True"; return $ LitBool True}
          <|> do {reserved "False"; return $ LitBool False}

recLit = litBool <|> litInteger

lit = do {Lit <$> recLit;}

lamAbs = do symbol "\\"
            i <- identifier
            reservedOp "."
            e <- expr
            return (Lam i e)

recIf = do
    reserved "if"
    e1 <- expr
    reserved "then"
    e2 <- expr
    reserved "else"
    If e1 e2 <$> expr

tup =
    parens (do {e1 <- expr; symbol ","; App (App (Const "(,)") e1) <$> expr;})
-- tup =
    --parens (do {e1 <- expr; symbol ","; e2 <- expr; return $ App (Const "(,)") (App e1 e2)})

recLet = do
    reserved "let"
    i <- identifier
    reservedOp "="
    e1 <- expr
    reserved "in"
    Let (i, e1) <$> expr

pvar i = do {return $ PVar i}

pcon i = do {PCon i <$> pats;}

pconTup = parens (do {p1 <- pat; symbol ","; p2 <- pat; return $ PCon "(,)" [p1, p2]})

pVarOrPCon = do
    i <- identifier
    if isLower (head i) then pvar i
    else pcon i

pConsLit = do {PLit <$> recLit;}

pats = do {p <- pat; ps <- pats; return (p:ps)}
      <|> return []

pat = pconTup
    <|> pVarOrPCon
    <|> pConsLit

patExpr = do
    p <- pat
    reservedOp "->"
    e <- expr
    return (p, e)

lpat = do {pe <- patExpr; pes <- maybePat; return (pe:pes)}

maybePat = do {symbol ";"; lpat;}
          <|> return []

caseof = do
    reserved "case"
    e <- expr
    reserved "of"
    symbol "{"
    lp <- lpat
    symbol "}"
    return $ Case e lp

parseNonApp = try (parens expr)  -- (E)
             <|> lamAbs          -- \x.E
             <|> varOrCons       -- x or X
             <|> try caseof      -- case E of {<lpat>}
             <|> recIf           -- if E then E else E
             <|> tup             -- (E, E)
             <|> try recLet      -- let x = E in E
             <|> lit             -- bool or int


----------------------------------------
parseLambda s = case parseExpr s of
                     Left er -> print er
                     Right e -> (print e >> print (infer e))

main = do putStr "Expression:"
          e <- getLine
          parseLambda e
