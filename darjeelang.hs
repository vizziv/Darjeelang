module Darjeelang where

import Prelude hiding (sum)
import Data.List hiding (sum)
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S

type DataName = String
type TagName = String
type VarName = String
type Prim = Integer

data Typ = TAny -- Just used in type checking (for now).
         | TPrim
         | TData DataName
         | TTag TagName Typ
         | TSum (S.Set Typ)
         | TProd (S.Set Typ)
         | TFun (S.Set Typ) Typ
         deriving (Eq, Ord, Show)

data Op = Plus | Minus | Times deriving Show

data ExpF e = EPrim Prim
            | EOp Op e e
            | EVar VarName
            | ETag TagName e
            | EUntag e
            | ESum (S.Set Typ) e
            | EProd [e]
            | EFun (M.Map Typ VarName) e
            | EApp e e
            | EBranch e e e
            | ELets [(Typ, VarName, e)] e
            | ECases e (M.Map Typ (VarName, e))
            | EMatch e (M.Map Typ VarName) e
            | ECast Typ e
            deriving Show

newtype Exp = E (ExpF Exp) deriving Show

data TypedExp = TE Typ (ExpF TypedExp) deriving Show

{-
We can handle the following errors but not gracefully.
 * Expressions are not well-typed.
 * Variables are not bound when referenced.
It might be necessary to give variables unique names, because closures aren't
yet very well tested.
-}

type TypContext = [(DataName, S.Set Typ)]

typCtx = [("List", S.fromList [TTag "Nil" TPrim,
                               TProd (S.fromList [TPrim, TData "List"])])]

type CheckContext = [(VarName, Typ)]

fromCtx ctx var = fromJust $ lookup var ctx
tryFromTypCtx typ@(TData dat) =
    case lookup dat typCtx of
      Nothing -> typ
      Just typs -> TSum typs
tryFromTypCtx typ = typ
tryFromTypCtxRev typ@(TSum typs) =
    case lookup typs (map (\(k,v) -> (v,k)) typCtx) of
      Nothing -> typ
      Just dat -> TData dat
tryFromTypCtxRev typ = typ

canonicalize t = tryFromTypCtxRev $
    case t of
      TTag name typ -> TTag name (canonicalize typ)
      TSum typs -> TSum (S.map canonicalize typs)
      TProd typs -> TProd (S.map canonicalize typs)
      TFun typs typ -> TFun (S.map canonicalize typs) (canonicalize typ)
      _ -> t

addArgsToCtx ctx args = map (\(typ, var) -> (var, typ)) (M.toList args) ++ ctx
addDeclsToCtx ctx decls = map (\(typ, var, _) -> (var, typ)) decls ++ ctx

argsTyps = M.keysSet

combine typ1 typ2 = case (typ1, typ2) of
                      (TAny, typ) -> typ
                      (typ, TAny) -> typ
                      -- Will add this when we can handle subtyping.
                      -- (TSum typs1, TSum typs2) -> TSum (S.union typs1 typs2)
                      _ -> if typ1 == typ2 then typ1 else error "combine"

checkUseArg typs typ = if S.member typ typs
                       then S.delete typ typs
                       else error "checkUseArg"

check :: CheckContext -> Exp -> TypedExp
check ctx (E e) =
    let ch = check ctx
        TE typ texp =
            case e of
              EPrim prim -> TE TPrim (EPrim prim)
              EOp op exp1 exp2 ->
                  let texp1@(TE typ1 _) = ch exp1
                      texp2@(TE typ2 _) = ch exp2
                  in case (typ1, typ2) of
                       (TPrim, TPrim) -> TE TPrim (EOp op texp1 texp2)
                       (TTag name _, TPrim) -> TE typ1 (ETag name (ch (E $
                           EOp op (E $ EUntag exp1) exp2)))
                       (TPrim, TTag name _) -> TE typ2 (ETag name (ch (E $
                           EOp op exp1 (E $ EUntag exp2))))
                       (TTag name1 _, TTag name2 _) ->
                           if name1 == name2
                           then TE typ1 (ETag name1 (ch (E $
                               EOp op (E $ EUntag exp1) (E $ EUntag exp2))))
                           else error "check EOp"
              ETag name exp ->
                  let texp@(TE typ _) = ch exp
                  in TE (TTag name typ) (ETag name texp)
              EUntag exp ->
                  let texp@(TE (TTag _ typ) _) = ch exp
                  in TE typ (EUntag texp)
              EVar var -> TE (fromCtx ctx var) (EVar var)
              ESum typs exp ->
                  let texp@(TE typ _) = ch exp
                  in if S.member typ typs
                     then TE (TSum typs) (ESum typs texp)
                     else error "check ESum"
              EProd exps ->
                  let texps = map ch exps
                      typs = S.fromList (map (\(TE typ _) -> typ) texps)
                  in if length texps == S.size typs
                     then TE (TProd typs) (EProd texps)
                     else error "check EProd"
              EFun args exp ->
                  let texp@(TE typ _) = check (addArgsToCtx ctx args) exp
                  in TE (TFun (argsTyps args) typ) (EFun args texp)
              EApp exp1 exp2 ->
                  let texp1@(TE (TFun typsA typZ) _) = ch exp1
                      texp2@(TE typ2 _) = ch exp2
                      typsB = checkUseArg typsA typ2
                      typ = if S.null typsB then typZ else TFun typsB typZ
                  in TE typ (EApp texp1 texp2)
              EBranch exp1 exp2 exp3 ->
                  let texp1@(TE TPrim _) = ch exp1
                      texp2@(TE typ2 _) = ch exp2
                      texp3@(TE typ3 _) = ch exp3
                  in TE (combine typ2 typ3) (EBranch texp1 texp2 texp3)
              ELets decls exp ->
                  let ch' = check (addDeclsToCtx ctx decls)
                      chDecl (typ, var, exp') =
                          let texp'@(TE typ' _) = ch' exp'
                          in if typ == typ'
                             then (typ,var,texp')
                             else error "check ELets"
                      texp@(TE typ _) = ch' exp
                  in TE typ (ELets (map chDecl decls) texp)
              ECases exp cases ->
                  let handleCase typAcc typC (var, exp) =
                          let texp@(TE typ _) = check ((var, typC) : ctx) exp
                          in (combine typAcc typ, (var, texp))
                      (typ, tcases) = M.mapAccumWithKey handleCase TAny cases
                      texp@(TE typSum _) = ch exp
                      TSum typs = tryFromTypCtx typSum
                  in if typs == M.keysSet cases
                     then TE typ (ECases texp tcases)
                     else error "check ECases"
              EMatch exp1 args exp2 ->
                  let texp1@(TE typ1@(TProd typs1) _) = ch exp1
                      texp2@(TE typ2 _) = check (addArgsToCtx ctx args) exp2
                  in if typs1 == M.keysSet args
                     then TE typ2 (EMatch texp1 args texp2)
                     else error "check EMatch"
    in TE (canonicalize typ) texp

data Value = VPrim Prim
           | VTag TagName Value
           | VSum Typ Value
           | VProd (M.Map Typ Value)
           | VFun EvalContext (M.Map Typ VarName) TypedExp
           deriving Show

type EvalContext = [(VarName, Value)]

applyOp Plus = (+)
applyOp Minus = (-)
applyOp Times = (*)

evalUseArg args (TE typ exp) =
    case M.lookup typ args of
      Nothing -> error "evalUseArg"
      Just var -> (var, M.delete typ args)

eval :: EvalContext -> TypedExp -> Value
eval ctx (TE t e) =
    let ev = eval ctx
    in case e of
         EPrim n -> VPrim n
         EOp op texp1 texp2 ->
             let VPrim n1 = ev texp1
                 VPrim n2 = ev texp2
             in VPrim (applyOp op n1 n2)
         ETag name texp -> VTag name (ev texp)
         EUntag texp -> let VTag _ val = ev texp in val
         EVar var -> fromCtx ctx var
         ESum typs texp@(TE typ _) -> VSum typ (ev texp)
         EProd texps -> VProd (M.fromList (map (\texp@(TE typ _) ->
                                                (typ, ev texp)) texps))
         EFun args texp -> VFun ctx args texp
         EApp texp1 texp2 ->
             let VFun ctx1 args1 texp1' = ev texp1
                 (var, args') = evalUseArg args1 texp2
                 ctx1' = (var, ev texp2) : ctx1
             in if M.null args'
                then eval ctx1' texp1'
                else VFun ctx1' args' texp1'
         EBranch texp1 texp2 texp3 ->
             let VPrim n1 = ev texp1
             in ev (if n1 == 0 then texp2 else texp3)
         ELets decls texp ->
             let ctx' = (map (\(_, var, texp') -> (var, eval ctx' texp'))
                         decls) ++ ctx
             in eval ctx' texp
         ECases texp@(TE typ _) cases ->
             let VSum typ val = ev texp
                 (var, texp') = fromJust (M.lookup typ cases)
             in eval ((var, val) : ctx) texp'
         EMatch texp1 args texp2 ->
              let VProd vals = ev texp1
                  ctx' = map snd (M.toList (M.intersectionWith (,)
                                            args vals)) ++ ctx
              in eval ctx' texp2

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
sum = e2 ESum . S.fromList
prod = E . EProd
fun = e2 EFun . M.fromList
infixl 8 %
(%) = e2 EApp
branch exp1 exp2 exp3 = E $ EBranch exp1 exp2 exp3
lets = e2 ELets
cases exp cs = E $ ECases exp (M.fromList
                               (map (\(typ, var, exp) -> (typ, (var, exp)))
                                cs))
match exp1 args exp2 = E $ EMatch exp1 (M.fromList args) exp2

tfun = TFun . S.fromList
tsum = TSum . S.fromList
tprod = TProd . S.fromList

-- Basic tests.
sub = fun [(TTag "fst" TPrim, "x"), (TTag "snd" TPrim, "y")]
          (untag (var "x") -~ untag (var "y"))
plus3 = fun [(TPrim, "x")] (var "x" +~ prim 3)
minus5 = fun [(TPrim, "x")] (var "x" -~ prim 5)
pick = fun [(TTag "choice" TPrim, "b"), (TPrim, "x")]
           ((branch (untag (var "b")) plus3 minus5) % var "x")
app = fun [(tfun [TPrim] TPrim, "f"), (TPrim, "x")] (var "f" % var "x")

-- Recursion.
factorial = lets [(tfun [TPrim] TPrim, "f",
                   fun [(TPrim, "x")]
                       (branch (var "x")
                               (prim 1)
                               (var "x" *~ var "f" % (var "x" -~ prim 1))))]
                 (var "f")
fibonacci = lets [(tfun [TTag "0" TPrim, TTag "1" TPrim, TPrim] TPrim, "f",
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

-- Cases and matches.
true = sum [ttrue, tfalse] (tag "True" (prim 0))
false = sum [ttrue, tfalse] (tag "False" (prim 0))
ttrue = TTag "True" TPrim
tfalse = TTag "False" TPrim
equal = fun [(TTag "Left" TPrim, "left"), (TTag "Right" TPrim, "right")]
            (branch (untag (var "left") -~ untag (var "right")) true false)
-- There will one day be syntactic sugar for things like equality.
eq x y = equal % (tag "Left" x) % (tag "Right" y)
exp2 = lets [(tfun [TPrim] TPrim, "exp2",
              fun [(TPrim, "x")]
                  (cases (eq (var "x") (prim 0))
                          [(ttrue, "_", prim 1),
                           (tfalse, "_", prim 2 *~
                                         var "exp2" % (var "x" -~ prim 1))]))]
            (var "exp2")
pythagoras = fun [(tprod [TTag "A" TPrim, TTag "B" TPrim], "ab")]
                 (match (var "ab") [(TTag "A" TPrim, "a"), (TTag "B" TPrim, "b")]
                        (untag (var "a" *~ var "a") +~ untag (var "b" *~ var "b")))

-- Data types.
tlist = TData "List"
nil = sum [tnil, tcons] (tag "Nil" (prim 0))
cons = (fun [(TPrim, "x"), (tlist, "xs")]
            (sum [tnil, tcons] (prod [var "x", var "xs"])))
tnil = TTag "Nil" TPrim
tcons = tprod [TPrim, tlist]
listMap = lets [(tfun [tlist, tfun [TPrim] TPrim] tlist, "map",
                 fun [(tfun [TPrim] TPrim, "f"), (tlist, "list")]
                     (cases (var "list")
                            [(tnil, "_", nil),
                             (tcons, "cons",
                              match (var "cons") [(TPrim, "x"), (tlist, "xs")]
                                    (cons % (var "f" % var "x")
                                          % (var "map" % var "xs" % var "f")))]))]
               (var "map")
list = cons % (cons % (cons % (cons % (cons % nil %
       prim 4) % prim 3) % prim 2) % prim 1) % prim 0
