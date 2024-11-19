module Lintings where

import AST
import Debug.Trace (traceShow)
import Distribution.TestSuite (TestInstance (name))
import LintTypes

--------------------------------------------------------------------------------
-- AUXILIARES
--------------------------------------------------------------------------------

-- Computa la lista de variables libres de una expresión
freeVariables :: Expr -> [Name]
freeVariables (Var name) = [name]
freeVariables (Lit _) = []
freeVariables (Infix _ e1 e2) = freeVariables e1 ++ freeVariables e2
freeVariables (App e1 e2) = freeVariables e1 ++ freeVariables e2
freeVariables (Lam name expr) = filter (/= name) (freeVariables expr)
freeVariables (Case e1 e2 (name1, name2, expr)) =
  freeVariables e1 ++ freeVariables e2 ++ filter (/= name2) (filter (/= name1) (freeVariables expr))
freeVariables (If cond e1 e2) = freeVariables cond ++ freeVariables e1 ++ freeVariables e2

lintEtaAux :: [Name] -> Linting Expr
lintEtaAux array (Lam x (App e1 (Var y))) =
  let (e1', l) = lintEtaAux array e1
   in if x == y && notElem x (freeVariables e1)
        then
          let res = e1'
           in (res, l ++ [LintEta (Lam x (App e1 (Var y))) res])
        else (Lam x (App e1' (Var y)), l)
lintEtaAux array (Lam x e) =
  let (e', l) = lintEtaAux (x : array) e
   in (Lam x e', l)
lintEtaAux array (App e1 e2) =
  let (e1', l1) = lintEtaAux array e1
      (e2', l2) = lintEtaAux array e2
   in (App e1' e2', l1 ++ l2)
lintEtaAux array (Infix op e1 e2) =
  let (e1', l1) = lintEtaAux array e1
      (e2', l2) = lintEtaAux array e2
   in (Infix op e1' e2', l1 ++ l2)
lintEtaAux array (Case e1 e2 (x, y, e3)) =
  let (e1', l1) = lintEtaAux array e1
      (e2', l2) = lintEtaAux array e2
      (e3', l3) = lintEtaAux (x : y : array) e3
   in (Case e1' e2' (x, y, e3'), l1 ++ l2 ++ l3)
lintEtaAux array (If cond e1 e2) =
  let (cond', l1) = lintEtaAux array cond
      (e1', l2) = lintEtaAux array e1
      (e2', l3) = lintEtaAux array e2
   in (If cond' e1' e2', l1 ++ l2 ++ l3)
lintEtaAux _ e = (e, [])

genericLintComp :: Linting Expr
genericLintComp (App v1 (App v2 x)) =
  let (v1', l1) = lintComp v1
   in let (v2', l2) = lintComp v2
       in let res = App (Infix Comp v1' v2') x
           in (res, l1 ++ l2 ++ [LintComp (App v1 (App v2 x)) res])

genericLintLamda :: Linting Expr -> Linting Expr
genericLintLamda f (Lam name e) =
  let (e', l) = f e
   in (Lam name e', l)

-- Los profes lo hicieron en 260 lineas de codigo aproximado

--------------------------------------------------------------------------------
-- LINTINGS
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Computación de constantes
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Reduce expresiones aritméticas/booleanas
-- Construye sugerencias de la forma (LintCompCst e r)
lintComputeConstant :: Linting Expr
lintComputeConstant (Infix o (Lit (LitInt l1)) (Lit (LitInt l2))) =
  let e = Infix o (Lit (LitInt l1)) (Lit (LitInt l2))
   in let r = case o of
            Add -> let res = Lit (LitInt (l1 + l2)) in (res, [LintCompCst e res])
            Sub ->
              if (l1 - l2) >= 0
                then let res = Lit (LitInt (l1 - l2)) in (res, [LintCompCst e res])
                else (e, [])
            Mult -> let res = Lit (LitInt (l1 * l2)) in (res, [LintCompCst e res])
            Div ->
              if l2 /= 0
                then let res = Lit (LitInt (l1 `div` l2)) in (res, [LintCompCst e res])
                else (e, [])
            Eq -> let res = Lit (LitBool (l1 == l2)) in (res, [LintCompCst e res])
            GTh -> let res = Lit (LitBool (l1 > l2)) in (res, [LintCompCst e res])
            LTh -> let res = Lit (LitBool (l1 < l2)) in (res, [LintCompCst e res])
       in r
lintComputeConstant (Infix o (Lit (LitBool l1)) (Lit (LitBool l2))) =
  let e = Infix o (Lit (LitBool l1)) (Lit (LitBool l2))
   in let r = case o of
            And -> let res = Lit (LitBool (l1 && l2)) in (res, [LintCompCst e res])
            Or -> let res = Lit (LitBool (l1 || l2)) in (res, [LintCompCst e res])
       in r
lintComputeConstant (Infix o (Lit l1) (Lit l2)) =
  let e = Infix o (Lit l1) (Lit l2) in (e, [])
lintComputeConstant (App e1 e2) =
  let (e1', ls1) = lintComputeConstant e1
   in let (e2', ls2) = lintComputeConstant e2
       in (App e1' e2', ls1 ++ ls2)
lintComputeConstant (Lam name e) =
  let (e', ls) = lintComputeConstant e
   in (Lam name e', ls)
lintComputeConstant (If e1 e2 e3) =
  let (e1', ls1) = lintComputeConstant e1
   in let (e2', ls2) = lintComputeConstant e2
       in let (e3', ls3) = lintComputeConstant e3
           in (If e1' e2' e3', ls1 ++ ls2 ++ ls3)
lintComputeConstant (Case e1 e2 (name1, name2, e3)) =
  let (e1', ls1) = lintComputeConstant e1
   in let (e2', ls2) = lintComputeConstant e2
       in let (e3', ls3) = lintComputeConstant e3
           in (Case e1' e2' (name1, name2, e3'), ls1 ++ ls2 ++ ls3)
lintComputeConstant (Infix o e1 e2) =
  let (e1', ls1) = lintComputeConstant e1
   in let (e2', ls2) = lintComputeConstant e2
       in if null ls1 && null ls2
            then
              (Infix o e1' e2', [])
            else
              let (e', ls) = lintComputeConstant (Infix o e1' e2') in (e', ls1 ++ ls2 ++ ls)
lintComputeConstant e = (e, [])

--------------------------------------------------------------------------------
-- Eliminación de chequeos redundantes de booleanos
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Elimina chequeos de la forma e == True, True == e, e == False y False == e
-- Construye sugerencias de la forma (LintBool e r)
lintRedBool :: Linting Expr
lintRedBool (Infix Eq (Lit (LitBool True)) e) =
  let t = Lit (LitBool True)
   in (e, [LintBool (Infix Eq t e) e])
lintRedBool (Infix Eq e (Lit (LitBool True))) =
  let t = Lit (LitBool True)
   in (e, [LintBool (Infix Eq e t) e])
lintRedBool (Infix Eq (Lit (LitBool False)) e) =
  let f = Lit (LitBool False)
   in let res = App (Var "not") e
       in (res, [LintBool (Infix Eq f e) res])
lintRedBool (Infix Eq e (Lit (LitBool False))) =
  let f = Lit (LitBool False)
   in let res = App (Var "not") e
       in (res, [LintBool (Infix Eq e f) res])
lintRedBool (App e1 e2) =
  let (e1', ls1) = lintRedBool e1
   in let (e2', ls2) = lintRedBool e2
       in (App e1' e2', ls1 ++ ls2)
lintRedBool (Lam name e) =
  let (e', l) = lintRedBool e
   in (Lam name e', l)
lintRedBool (If e1 e2 e3) =
  let (e1', ls1) = lintRedBool e1
   in let (e2', ls2) = lintRedBool e2
       in let (e3', ls3) = lintRedBool e3
           in (If e1' e2' e3', ls1 ++ ls2 ++ ls3)
lintRedBool (Case e1 e2 (name1, name2, e3)) =
  let (e1', ls1) = lintRedBool e1
   in let (e2', ls2) = lintRedBool e2
       in let (e3', ls3) = lintRedBool e3
           in (Case e1' e2' (name1, name2, e3'), ls1 ++ ls2 ++ ls3)
lintRedBool (Infix o e1 e2) =
  let (e1', ls1) = lintRedBool e1
   in let (e2', ls2) = lintRedBool e2
       in if null ls1 && null ls2
            then
              (Infix o e1' e2', [])
            else
              let (e', ls) = lintRedBool (Infix o e1' e2') in (e', ls1 ++ ls2 ++ ls)
lintRedBool e = (e, [])

--------------------------------------------------------------------------------
-- Eliminación de if redundantes
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Sustitución de if con literal en la condición por la rama correspondiente
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfCond :: Linting Expr
lintRedIfCond (If (Lit (LitBool True)) e2 e3) =
  let (e2', l2) = lintRedIfCond e2
   in let (e3', l3) = lintRedIfCond e3
       in (e2', l2 ++ l3 ++ [LintRedIf (If (Lit (LitBool True)) e2' e3') e2'])
lintRedIfCond (If (Lit (LitBool False)) e2 e3) =
  let (e2', l2) = lintRedIfCond e2
   in let (e3', l3) = lintRedIfCond e3
       in (e3', l2 ++ l3 ++ [LintRedIf (If (Lit (LitBool False)) e2' e3') e3'])
lintRedIfCond (If e1 e2 e3) =
  let (e1', ls1) = lintRedIfCond e1
   in let (e2', ls2) = lintRedIfCond e2
       in let (e3', ls3) = lintRedIfCond e3
           in (If e1' e2' e3', ls1 ++ ls2 ++ ls3)
lintRedIfCond (App e1 e2) =
  let (e1', l1) = lintRedIfCond e1
   in let (e2', l2) = lintRedIfCond e2
       in (App e1' e2', l1 ++ l2)
lintRedIfCond (Lam name e) =
  let (e', l) = lintRedIfCond e
   in (Lam name e', l)
lintRedIfCond (Case e1 e2 (name1, name2, e3)) =
  let (e1', l1) = lintRedIfCond e1
   in let (e2', l2) = lintRedIfCond e2
       in let (e3', l3) = lintRedIfCond e3
           in (Case e1' e2' (name1, name2, e3'), l1 ++ l2 ++ l3)
lintRedIfCond (Infix o e1 e2) =
  let (e1', l1) = lintRedIfCond e1
   in let (e2', l2) = lintRedIfCond e2
       in (Infix o e1' e2', l1 ++ l2)
lintRedIfCond e = (e, [])

--------------------------------------------------------------------------------
-- Sustitución de if por conjunción entre la condición y su rama _then_
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfAnd :: Linting Expr
lintRedIfAnd (If c e1 (Lit (LitBool False))) =
  let (c', l1) = lintRedIfAnd c
   in let (e1', l2) = lintRedIfAnd e1
       in let res = Infix And c' e1'
           in (res, l1 ++ l2 ++ [LintRedIf (If c' e1' (Lit (LitBool False))) res])
lintRedIfAnd (If e1 e2 e3) =
  let (e1', ls1) = lintRedIfAnd e1
   in let (e2', ls2) = lintRedIfAnd e2
       in let (e3', ls3) = lintRedIfAnd e3
           in (If e1' e2' e3', ls1 ++ ls2 ++ ls3)
lintRedIfAnd (App e1 e2) =
  let (e1', l1) = lintRedIfAnd e1
   in let (e2', l2) = lintRedIfAnd e2
       in (App e1' e2', l1 ++ l2)
lintRedIfAnd (Lam name e) =
  let (e', l) = lintRedIfAnd e
   in (Lam name e', l)
lintRedIfAnd (Case e1 e2 (name1, name2, e3)) =
  let (e1', l1) = lintRedIfAnd e1
   in let (e2', l2) = lintRedIfAnd e2
       in let (e3', l3) = lintRedIfAnd e3
           in (Case e1' e2' (name1, name2, e3'), l1 ++ l2 ++ l3)
lintRedIfAnd (Infix o e1 e2) =
  let (e1', l1) = lintRedIfAnd e1
   in let (e2', l2) = lintRedIfAnd e2
       in (Infix o e1' e2', l1 ++ l2)
lintRedIfAnd e = (e, [])

--------------------------------------------------------------------------------
-- Sustitución de if por disyunción entre la condición y su rama _else_
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfOr :: Linting Expr
lintRedIfOr (If c (Lit (LitBool True)) e) =
  let (c', l1) = lintRedIfOr c
   in let (e', l2) = lintRedIfOr e
       in let res = Infix Or c' e'
           in (res, l1 ++ l2 ++ [LintRedIf (If c' (Lit (LitBool True)) e') res])
lintRedIfOr (If e1 e2 e3) =
  let (e1', ls1) = lintRedIfOr e1
   in let (e2', ls2) = lintRedIfOr e2
       in let (e3', ls3) = lintRedIfOr e3
           in (If e1' e2' e3', ls1 ++ ls2 ++ ls3)
lintRedIfOr (App e1 e2) =
  let (e1', l1) = lintRedIfOr e1
   in let (e2', l2) = lintRedIfOr e2
       in (App e1' e2', l1 ++ l2)
lintRedIfOr (Lam name e) =
  let (e', l) = lintRedIfOr e
   in (Lam name e', l)
lintRedIfOr (Case e1 e2 (name1, name2, e3)) =
  let (e1', l1) = lintRedIfOr e1
   in let (e2', l2) = lintRedIfOr e2
       in let (e3', l3) = lintRedIfOr e3
           in (Case e1' e2' (name1, name2, e3'), l1 ++ l2 ++ l3)
lintRedIfOr (Infix o e1 e2) =
  let (e1', l1) = lintRedIfOr e1
   in let (e2', l2) = lintRedIfOr e2
       in (Infix o e1' e2', l1 ++ l2)
lintRedIfOr e = (e, [])

--------------------------------------------------------------------------------
-- Chequeo de lista vacía
--------------------------------------------------------------------------------
-- Sugiere el uso de null para verificar si una lista es vacía
-- Construye sugerencias de la forma (LintNull e r)

lintNull :: Linting Expr
lintNull (Infix Eq e1 (Lit LitNil)) =
  let (e1', l1) = lintNull e1
   in let res = App (Var "null") e1'
       in (res, l1 ++ [LintNull (Infix Eq e1' (Lit LitNil)) res])
lintNull (Infix Eq (Lit LitNil) e1) =
  let (e1', l1) = lintNull e1
   in let res = App (Var "null") e1'
       in (res, l1 ++ [LintNull (Infix Eq (Lit LitNil) e1') res])
lintNull (Infix Eq (App (Var "length") e1) (Lit (LitInt 0))) =
  let (e1', l1) = lintNull e1
   in let res = App (Var "null") e1'
       in (res, l1 ++ [LintNull (Infix Eq (App (Var "length") e1') (Lit (LitInt 0))) res])
lintNull (Infix Eq (Lit (LitInt 0)) (App (Var "length") e1)) =
  let (e1', l1) = lintNull e1
   in let res = App (Var "null") e1'
       in (res, l1 ++ [LintNull (Infix Eq (Lit (LitInt 0)) (App (Var "length") e1')) res])
lintNull (App e1 e2) =
  let (e1', l1) = lintNull e1
   in let (e2', l2) = lintNull e2
       in (App e1' e2', l1 ++ l2)
lintNull (Lam name e) =
  let (e', l) = lintNull e
   in (Lam name e', l)
lintNull (If e1 e2 e3) =
  let (e1', l1) = lintNull e1
   in let (e2', l2) = lintNull e2
       in let (e3', l3) = lintNull e3
           in (If e1' e2' e3', l1 ++ l2 ++ l3)
lintNull (Infix o e1 e2) =
  let (e1', l1) = lintNull e1
   in let (e2', l2) = lintNull e2
       in (Infix o e1' e2', l1 ++ l2)
lintNull (Case e1 e2 (n1, n2, e3)) =
  let (e1', l1) = lintNull e1
   in let (e2', l2) = lintNull e2
       in let (e3', l3) = lintNull e3
           in (Case e1' e2' (n1, n2, e3'), l1 ++ l2 ++ l3)
lintNull e = (e, [])

--------------------------------------------------------------------------------
-- Eliminación de la concatenación
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (e:[] ++ es), reemplazando por (e:es)
-- Construye sugerencias de la forma (LintAppend e r)

lintAppend :: Linting Expr
lintAppend (Infix Append (Infix Cons e1 (Lit LitNil)) e2) =
  let (e1', l1) = lintAppend e1
   in let (e2', l2) = lintAppend e2
       in let res = Infix Cons e1' e2'
           in (res, l1 ++ l2 ++ [LintAppend (Infix Append (Infix Cons e1' (Lit LitNil)) e2') res])
lintAppend (Infix o e1 e2) =
  let (e1', l1) = lintAppend e1
   in let (e2', l2) = lintAppend e2
       in (Infix o e1' e2', l1 ++ l2)
lintAppend (App e1 e2) =
  let (e1', l1) = lintAppend e1
   in let (e2', l2) = lintAppend e2
       in (App e1' e2', l1 ++ l2)
lintAppend (Lam name e) =
  let (e', l) = lintAppend e
   in (Lam name e', l)
lintAppend (If e1 e2 e3) =
  let (e1', l1) = lintAppend e1
   in let (e2', l2) = lintAppend e2
       in let (e3', l3) = lintAppend e3
           in (If e1' e2' e3', l1 ++ l2 ++ l3)
lintAppend (Case e1 e2 (n1, n2, e3)) =
  let (e1', l1) = lintAppend e1
   in let (e2', l2) = lintAppend e2
       in let (e3', l3) = lintAppend e3
           in (Case e1' e2' (n1, n2, e3'), l1 ++ l2 ++ l3)
lintAppend e = (e, [])

--------------------------------------------------------------------------------
-- Composición
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (f (g t)), reemplazando por (f . g) t
-- Construye sugerencias de la forma (LintComp e r)

lintComp :: Linting Expr
lintComp (App v1 (App v2 (Lit x))) =
  genericLintComp (App v1 (App v2 (Lit x)))
lintComp (App v1 (App v2 (Var x))) =
  genericLintComp (App v1 (App v2 (Var x)))
lintComp (App v1 (App (Infix Comp e1 e2) v2)) =
  let (e1', le1) = lintComp e1
   in let (e2', le2) = lintComp e2
       in let (v1', l1) = lintComp v1
           in let (v2', l2) = lintComp v2
               in let res = App (Infix Comp v1' (Infix Comp e1' e2')) v2'
                   in (res, le1 ++ le2 ++ l1 ++ l2 ++ [LintComp (App v1' (App (Infix Comp e1' e2') v2')) res])
lintComp (App v1 (App v2 (Infix o e1 e2))) =
  let (e1', le1) = lintComp e1
   in let (e2', le2) = lintComp e2
       in let (v1', l1) = lintComp v1
           in let (v2', l2) = lintComp v2
               in let res = Infix Comp v1' v2'
                   in (App res (Infix o e1' e2'), le1 ++ le2 ++ l1 ++ l2 ++ [LintComp (App v1 (App v2 (Infix o e1' e2'))) (App res (Infix o e1' e2'))])
lintComp (App v1 (App v2 e2)) =
  let (vx', lx) = lintComp (App v2 e2)
   in let (v1', l1) = lintComp v1
       in let (vy', ly) = lintComp (App v1' vx')
           in (vy', lx ++ l1 ++ ly)
lintComp (Lam name e) =
  let (e', l) = lintComp e
   in (Lam name e', l)
lintComp (If e1 e2 e3) =
  let (e1', l1) = lintComp e1
   in let (e2', l2) = lintComp e2
       in let (e3', l3) = lintComp e3
           in (If e1' e2' e3', l1 ++ l2 ++ l3)
lintComp (Case e1 e2 (n1, n2, e3)) =
  let (e1', l1) = lintComp e1
   in let (e2', l2) = lintComp e2
       in let (e3', l3) = lintComp e3
           in (Case e1' e2' (n1, n2, e3'), l1 ++ l2 ++ l3)
lintComp e = (e, [])

--------------------------------------------------------------------------------
-- Eta Redución
--------------------------------------------------------------------------------
-- se aplica en casos de la forma \x -> e x, reemplazando por e
-- Construye sugerencias de la forma (LintEta e r)

lintEta :: Linting Expr
lintEta e = lintEtaAux (freeVariables e) e

--------------------------------------------------------------------------------
-- Eliminación de recursión con map
--------------------------------------------------------------------------------

-- Sustituye recursión sobre listas por `map`
-- Construye sugerencias de la forma (LintMap f r)
lintMap :: Linting FunDef
lintMap (FunDef func (Lam l1 (Case (Var l2) (Lit LitNil) (x, xs, Infix Cons e (App (Var func2) (Var xs2)))))) =
  let og = FunDef func (Lam l1 (Case (Var l2) (Lit LitNil) (x, xs, Infix Cons e (App (Var func2) (Var xs2)))))
   in let vlibres = freeVariables e
       in if func == func2 && l1 == l2 && xs == xs2 && notElem xs vlibres && notElem func vlibres && notElem l1 vlibres
            then
              (FunDef func (App (Var "map") (Lam x e)), [LintMap og (FunDef func (App (Var "map") (Lam x e)))])
            else (og, [])
lintMap e = (e, [])

--------------------------------------------------------------------------------
-- Combinación de Lintings
--------------------------------------------------------------------------------

-- Dada una transformación a nivel de expresión, se construye
-- una transformación a nivel de función
liftToFunc :: Linting Expr -> Linting FunDef
liftToFunc lt (FunDef name expr) =
  let (expr', ls) = lt expr
   in (FunDef name expr', ls)

-- encadenar transformaciones:
(>==>) :: Linting a -> Linting a -> Linting a
lint1 >==> lint2 = \input ->
  let (a, ls1) = lint1 input
      (a', ls2) = lint2 a
   in (a', ls1 ++ ls2)

-- aplica las transformaciones 'lints' repetidas veces y de forma incremental,
-- hasta que ya no generen más cambios en 'func'
lintRec :: Linting a -> Linting a
lintRec lints func =
  let (a, ls1) = lints func
   in if null ls1
        then (a, ls1)
        else
          let (a', ls2) = lintRec lints a
           in (a', ls1 ++ ls2)
