module Lintings where

import AST
import Distribution.TestSuite (TestInstance (name))
import LintTypes

--------------------------------------------------------------------------------
-- AUXILIARES
--------------------------------------------------------------------------------

-- Computa la lista de variables libres de una expresión
freeVariables :: Expr -> [Name]
freeVariables = undefined

-- Linting extra
-- lintBool (Infix Or (Lit (LitBool True)) e) =
--   let t = Lit (LitBool True)
--    in (t, [LintBool (Infix Or t e) t])
-- lintBool (Infix Or e (Lit (LitBool True))) =
--   let t = Lit (LitBool True)
--    in (t, [LintBool (Infix Or e t) t])
-- lintBool (Infix And (Lit (LitBool False)) e) =
--   let f = Lit (LitBool False)
--    in (f, [LintBool (Infix And f e) f])
-- lintBool (Infix And e (Lit (LitBool False))) =
--   let f = Lit (LitBool False)
--    in (f, [LintBool (Infix And e f) f])

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
-- lintComputeConstant (Lit l) = (Lit l, [])
-- lintComputeConstant (Var name) = (Var name, [])
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
lintRedBool (Lam name e) = lintRedBool e
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
-- lintRedBool (Lit l) = (Lit l, [])
-- lintRedBool (Var name) = (Var name, [])
lintRedBool e = (e, [])

--------------------------------------------------------------------------------
-- Eliminación de if redundantes
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Sustitución de if con literal en la condición por la rama correspondiente
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfCond :: Linting Expr
lintRedIfCond = undefined

--------------------------------------------------------------------------------
-- Sustitución de if por conjunción entre la condición y su rama _then_
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfAnd :: Linting Expr
lintRedIfAnd = undefined

--------------------------------------------------------------------------------
-- Sustitución de if por disyunción entre la condición y su rama _else_
-- Construye sugerencias de la forma (LintRedIf e r)
lintRedIfOr :: Linting Expr
lintRedIfOr = undefined

--------------------------------------------------------------------------------
-- Chequeo de lista vacía
--------------------------------------------------------------------------------
-- Sugiere el uso de null para verificar si una lista es vacía
-- Construye sugerencias de la forma (LintNull e r)

lintNull :: Linting Expr
lintNull = undefined

--------------------------------------------------------------------------------
-- Eliminación de la concatenación
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (e:[] ++ es), reemplazando por (e:es)
-- Construye sugerencias de la forma (LintAppend e r)

lintAppend :: Linting Expr
lintAppend = undefined

--------------------------------------------------------------------------------
-- Composición
--------------------------------------------------------------------------------
-- se aplica en casos de la forma (f (g t)), reemplazando por (f . g) t
-- Construye sugerencias de la forma (LintComp e r)

lintComp :: Linting Expr
lintComp = undefined

--------------------------------------------------------------------------------
-- Eta Redución
--------------------------------------------------------------------------------
-- se aplica en casos de la forma \x -> e x, reemplazando por e
-- Construye sugerencias de la forma (LintEta e r)

lintEta :: Linting Expr
lintEta = undefined

--------------------------------------------------------------------------------
-- Eliminación de recursión con map
--------------------------------------------------------------------------------

-- Sustituye recursión sobre listas por `map`
-- Construye sugerencias de la forma (LintMap f r)
lintMap :: Linting FunDef
lintMap = undefined

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
