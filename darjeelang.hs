module Darjeelang where

import Data.Function
import Data.List
import Data.Maybe

type TagName = String
type VarName = String

data Typ = TPrim
         | TTag TagName Typ
         | TFun [Typ] Typ
         deriving (Eq, Show)

data Op = Plus | Minus | Times deriving Show

data ExpF e = EPrim Integer
            | EOp Op e e
            | ETag TagName e
            | EUntag e
            | EVar VarName
            | EFun [(Typ, VarName)] e
            | EApp e e
            | EBranch e e e
            | ELets [(Typ, VarName, e)] e
            deriving Show

newtype Exp = E (ExpF Exp) deriving Show

data TypedExp = TE Typ (ExpF TypedExp) deriving Show

{-
For now, we handle things nicely only if the following hold.
 * Argument type lists always appear in the same order.
 * Lists of single values have no duplicates.
 * Lists of tuples have no duplicate first members.
 * Variable names are unique (might be unnecessary, actually).
We can handle the following errors but not gracefully.
 * Expressions are not well-typed.
 * Variables are not bound when referenced.
-}

type CheckContext = [(VarName, Typ)]

fromCtx ctx var = fromJust $ lookup var ctx

addArgsToCtx ctx args = map (\(typ,var) -> (var,typ)) args ++ ctx
addDeclsToCtx ctx decls = map (\(typ,var,_) -> (var,typ)) decls ++ ctx

argsTyps = map fst

checkUseArg typs typ =
    case find (==typ) typs of
      Nothing -> undefined
      Just _ -> delete typ typs

check :: CheckContext -> Exp -> TypedExp
check ctx (E e) =
    let ch = check ctx
    in case e of
         EPrim prim -> TE TPrim (EPrim prim)
         EOp op exp1 exp2 ->
             let texp1@(TE TPrim _) = ch exp1
                 texp2@(TE TPrim _) = ch exp2
             in TE TPrim (EOp op texp1 texp2)
         ETag name exp ->
             let texp@(TE typ _) = ch exp
             in TE (TTag name typ) (ETag name texp)
         EUntag exp ->
             let texp@(TE (TTag _ typ) _) = ch exp
             in TE typ (EUntag texp)
         EVar var -> TE (fromCtx ctx var) (EVar var)
         EFun args exp ->
             let texp@(TE typ _) = check (addArgsToCtx ctx args) exp
             in TE (TFun (argsTyps args) typ) (EFun args texp)
         EApp exp1 exp2 ->
             let texp1@(TE (TFun typsA typZ) _) = ch exp1
                 texp2@(TE typ2 _) = ch exp2
                 typsB = checkUseArg typsA typ2
                 typ = case typsB of
                         [] -> typZ
                         _ -> TFun typsB typZ
             in TE typ (EApp texp1 texp2)
         EBranch exp1 exp2 exp3 ->
             let texp1@(TE TPrim _) = ch exp1
                 texp2@(TE typ2 _) = ch exp2
                 texp3@(TE typ3 _) = ch exp3
             in if typ2 == typ3
                then TE typ2 (EBranch texp1 texp2 texp3)
                else undefined
         ELets decls exp ->
             let ch' = check (addDeclsToCtx ctx decls)
                 chDecl (typ,var,exp') = let texp'@(TE typ' _) = ch' exp'
                                         in if typ == typ'
                                            then (typ,var,texp')
                                            else undefined
                 texp@(TE typ _) = ch' exp
             in TE typ (ELets (map chDecl decls) texp)

data Result = RPrim Integer
            | RTag TagName Result
            | RFun EvalContext [(Typ, VarName)] TypedExp
            deriving Show

type EvalContext = [(VarName, Result)]

applyOp Plus = (+)
applyOp Minus = (-)
applyOp Times = (*)

evalUseArg args (TE typ exp) =
    case lookup typ args of
      Nothing -> undefined
      Just var -> (var, delete (typ, var) args)

-- Assumes expressions are well-typed, e.g. EOps are applied only to EPrims.
eval :: EvalContext -> TypedExp -> Result
eval ctx (TE t e) =
    let ev = eval ctx
    in case e of
         EPrim n -> RPrim n
         EOp op texp1 texp2 ->
             let RPrim n1 = ev texp1
                 RPrim n2 = ev texp2
             in RPrim (applyOp op n1 n2)
         ETag name texp -> RTag name (ev texp)
         EUntag texp -> let RTag _ result = ev texp in result
         EVar var -> fromCtx ctx var
         EFun args texp -> RFun ctx args texp
         EApp texp1 texp2 ->
             let RFun ctx1 args1 texp1' = ev texp1
                 (var, args') = evalUseArg args1 texp2
                 ctx1' = (var, ev texp2) : ctx1
             in case args' of
                  [] -> eval ctx1' texp1'
                  _ -> RFun ctx1' args' texp1'
         EBranch texp1 texp2 texp3 ->
             let RPrim n1 = ev texp1
             in ev (if n1 == 0 then texp2 else texp3)
         ELets decls texp ->
             let ctx' = map (\(_,var,texp') -> (var, eval ctx' texp')) decls ++ ctx
             in eval ctx' texp

run = eval [] . check []

e2 con x y = E $ con x y
prim = E . EPrim
infixl 6 +~
(+~) = e2 $ EOp Plus
infixl 6 -~
(-~) = e2 $ EOp Minus
infixl 6 *~
(*~) = e2 $ EOp Times
var = E . EVar
tag = e2 ETag
untag = E . EUntag
fun = e2 EFun
infixl 8 %
(%) = e2 EApp
branch exp1 exp2 exp3 = E $ EBranch exp1 exp2 exp3
lets = e2 ELets

sub = fun [(TTag "fst" TPrim, "x"), (TTag "snd" TPrim, "y")]
          (untag (var "x") -~ untag (var "y"))
plus3 = fun [(TPrim, "x")] (var "x" +~ prim 3)
minus5 = fun [(TPrim, "x")] (var "x" -~ prim 5)
pick = fun [(TTag "choice" TPrim, "b"), (TPrim, "x")]
           ((branch (untag (var "b")) plus3 minus5) % var "x")
app = fun [(TFun [TPrim] TPrim, "f"), (TPrim, "x")] (var "f" % var "x")
factorial = lets [(TFun [TPrim] TPrim, "f",
                   fun [(TPrim, "x")]
                       (branch (var "x")
                               (prim 1)
                               (var "x" *~ var "f" % (var "x" -~ prim 1))))]
                 (var "f")
fibonacci = lets [(TFun [TTag "0" TPrim, TTag "1" TPrim, TPrim] TPrim, "f",
                   fun [(TTag "0" TPrim, "y"),
                        (TTag "1" TPrim, "z"),
                        (TPrim, "x")]
                        (branch (var "x")
                                (untag (var "y"))
                               (var "f" % tag "0" (untag (var "z")) %
                                          tag "1" (untag (var "y") +~
                                                   untag (var "z")) %
                                          (var "x" -~ prim 1))))]
                 (var "f" % tag "0" (prim 0) % tag "1" (prim 1))
