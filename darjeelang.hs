{-# LANGUAGE
  NoMonomorphismRestriction,
  TupleSections #-}

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

data ExpF t e = EPrim Integer
              | EOp Op e e
              | ETag TagName e
              | EUntag TagName e
              | EVar VarName
              | EFun [(t, VarName)] e
              | EApp e e
              deriving Show

newtype Exp = E (ExpF Typ Exp) deriving Show

data TypedExp = TE Typ (ExpF Typ TypedExp) deriving Show

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

addArgsToCtx ctx args = (map (\(x,y) -> (y,x)) args) ++ ctx

argsTyps = map fst

checkUseArg typs typ =
    case find (==typ) typs of
      Nothing -> undefined
      Just _ -> delete typ typs

check :: CheckContext -> Exp -> TypedExp
check ctx (E e) =
    case e of
      EPrim prim -> TE TPrim (EPrim prim)
      EOp op exp1 exp2 -> let texp1@(TE TPrim _) = check ctx exp1
                              texp2@(TE TPrim _) = check ctx exp2
                          in TE TPrim (EOp op texp1 texp2)
      ETag name exp -> let texp@(TE typ _) = check ctx exp
                      in TE (TTag name typ) (ETag name texp)
      EUntag name exp -> let texp@(TE (TTag name' typ) _) = check ctx exp
                         in if name == name'
                            then TE typ (EUntag name texp)
                            else undefined
      EVar var -> TE (fromCtx ctx var) (EVar var)
      EFun args exp -> let texp@(TE typ _) = check (addArgsToCtx ctx args) exp
                       in TE (TFun (argsTyps args) typ) (EFun args texp)
      EApp exp1 exp2 -> let texp1@(TE (TFun typsA typZ) _) = check ctx exp1
                            texp2@(TE typ2 _) = check ctx exp2
                            typsB = checkUseArg typsA typ2
                            typ = case typsB of
                                    [] -> typZ
                                    _ -> TFun typsB typZ
                        in TE typ (EApp texp1 texp2)

applyOp Plus = (+)
applyOp Minus = (-)
applyOp Times = (*)

data Result = RPrim Integer
            | RTag TagName Result
            | RFun EvalContext [(Typ, VarName)] TypedExp
            deriving Show

type EvalContext = [(VarName, Result)]

evalUseArg args (TE typ exp) =
    case lookup typ args of
      Nothing -> undefined
      Just var -> (var, delete (typ, var) args)

-- Assumes expressions are well-typed, e.g. EOps are applied only to EPrims.
eval :: EvalContext -> TypedExp -> Result
eval ctx (TE t e) =
    case e of
      EPrim n -> RPrim n
      EOp op texp1 texp2 -> let RPrim n1 = eval ctx texp1
                                RPrim n2 = eval ctx texp2
                            in RPrim (applyOp op n1 n2)
      ETag name texp -> RTag name (eval ctx texp)
      EUntag name texp -> let RTag _ result = eval ctx texp in result
      EVar var -> fromCtx ctx var
      EFun args texp -> RFun ctx args texp
      EApp texp1 texp2 -> let RFun ctx1 args1 texp1' = eval ctx texp1
                              (var, args') = evalUseArg args1 texp2
                              ctx1' = (var, eval ctx texp2) : ctx1
                          in case args' of
                               [] -> eval ctx1' texp1'
                               _ -> RFun ctx1' args' texp1'

e2 con x y = E $ con x y
prim = E . EPrim
(+~) = e2 $ EOp Plus
(-~) = e2 $ EOp Minus
(*~) = e2 $ EOp Times
var = E . EVar
tag = e2 ETag
untag = e2 EUntag
fun = e2 EFun
(%) = e2 EApp

expSubtract = fun [(TTag "fst" TPrim, "x"), (TTag "snd" TPrim, "y")] $
                  untag "fst" (var "x") -~ untag "snd" (var "y")
exp5 = expSubtract % tag "snd" (prim 4) % tag "fst" (prim 9)
expNegative5 = expSubtract % tag "fst" (prim 4) % tag "snd" (prim 9)

expApply = fun [(TFun [TPrim] TPrim, "f"), (TPrim, "x")] (var "f" % var "x")
exp6 = expApply % prim 2 % fun [(TPrim, "x")] (prim 3 *~ var "x")
