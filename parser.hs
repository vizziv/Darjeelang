{-# LANGUAGE NoMonomorphismRestriction #-}

module Parser where

import Debug.Trace

import Prelude hiding (exp)
import Control.Applicative
import Control.Monad
import qualified Data.Map as M
import qualified Data.Set as S
import Text.Parsec hiding ((<|>), optional, many, parse)
import qualified Text.Parsec as Parsec (parse)
import Text.Parsec.Expr
import qualified Text.Parsec.Token as P
import Darjeelang

lang = P.LanguageDef {P.commentStart = "{-",
                      P.commentEnd = "-}",
                      P.commentLine = "--",
                      P.nestedComments = True,
                      P.identStart = letter <|> char '_',
                      P.identLetter = alphaNum <|> char '_',
                      P.opStart = oneOf "!#$%&*+./<=>?@^|-~",
                      P.opLetter = oneOf "#$%*+./<=>?^|-~", -- No prefixes.
                      P.reservedNames = ["let", "data", "in", "case", "of",
                                         "match", "with", "branch", "zero",
                                         "nonzero", "Int", "__"],
                      P.reservedOpNames = ["+", "-", "*", "~", "!", "@", "&",
                                           "->", "="],
                      P.caseSensitive = True}

lexer = P.makeTokenParser lang
identifier = P.identifier lexer
reserved = P.reserved lexer
operator = P.operator lexer
reservedOp = P.reservedOp lexer
natural = P.natural lexer
parens = P.parens lexer
braces = P.braces lexer
angles = P.angles lexer
brackets = P.brackets lexer
symbol = P.symbol lexer
colon = P.colon lexer
commaSep = P.commaSep lexer
semi = P.semi lexer
semiSep = P.semiSep lexer

ops = [Infix (pure (e2 EApp)) AssocLeft] :
      (map . map)
      (\(op, assoc, fun) -> Infix (reservedOp op *> pure fun) assoc)
      [[("*", AssocLeft, e2 $ EOp Times)],
       [("+", AssocLeft, e2 $ EOp Plus), ("-", AssocLeft, e2 $ EOp Minus)]]

typ = choice
      [parens typ,
       TPrim <$ reserved "Int",
       try $ TTag <$> identifier <* reservedOp "~" <*> typ,
       TData <$> identifier,
       TSum <$ reservedOp "@" <*> typs,
       TProd <$ reservedOp "&" <*> typs,
       TFun <$> typs <* reservedOp "->" <*> typ]

typs = S.fromList <$> braces (commaSep typ)

funDecl = do
  result <- typ
  colon
  var <- identifier
  args <- M.fromList <$> (braces . commaSep)
          ((,) <$> typ <* colon <*> identifier)
  reservedOp "="
  body <- exp
  return (TFun (M.keysSet args) result, var, E $ EFun args body)

matchCase = do
  reservedOp "&"
  args <- M.fromList <$> (braces . commaSep)
          ((,) <$> typ <* colon <*> identifier)
  reservedOp "->"
  body <- exp
  return (TProd (M.keysSet args), ("__", E $ EMatch (E $ EVar "__") args body))

exp = buildExpressionParser ops term

term = (parens exp <|>) . (E <$>) $ choice
       [EPrim <$> natural,
        try $ ETag <$> identifier <* reservedOp "~" <*> term,
        EVar <$> identifier,
        EUntag <$ reservedOp "!" <*> term,
        ESum <$ reservedOp "@" <*> (Left <$> identifier <|>
                                    Right <$> typs) <*> term,
        EProd <$ reservedOp "&" <*> braces (commaSep exp),
        EBranch <$ reserved "branch" <*> exp <*
                   reserved "zero" <*> exp <*
                   reserved "nonzero" <*> exp,
        (\b n z -> EBranch b z n) <$ reserved "branch" <*> exp <*
                                     reserved "nonzero" <*> exp <*
                                     reserved "zero" <*> exp,
        EFun . M.fromList <$> (braces . commaSep)
                               ((,) <$> typ <* colon <*> identifier) <*
                              reservedOp "->" <*> exp,
        ELets <$ reserved "let" <*> (braces . ((optional semi) *>) . semiSep)
                  (try funDecl <|>
                   (,,) <$> typ <* colon <*> identifier <*
                   reservedOp "=" <*> exp) <*
                 reserved "in" <*> exp,
        ECases <$ reserved "case" <*> exp <* reserved "of" <*>
                   ((M.fromList <$>) . braces . ((optional semi) *>) . semiSep)
                   (try matchCase <|> (,) <$> typ <* colon <*>
                    ((,) <$> identifier <* reservedOp "->" <*> exp)),
        EMatch <$ reserved "match" <*> exp <* reserved "with" <*
               reservedOp "&" <*> ((M.fromList <$>) . braces . commaSep)
                              ((,) <$> typ <* colon <*> identifier) <*
                              reservedOp "->" <*> exp,
        EDatas <$ reserved "data" <*> (braces . ((optional semi) *>) . semiSep)
                   ((,) <$> identifier <*
                    reservedOp "=" <* reservedOp "@" <*> typs) <*
                  reserved "in" <*> exp]

decomment = many $ choice $ map try
            [(string "{-" <* manyTill anyToken (string "-}")) *> pure '\n',
             (string "--" <* manyTill anyToken endOfLine) *> pure '\n',
             anyToken]

layout lines =
    let avoidSemi nextLine =
            case dropWhile (==' ') nextLine of
              "" -> True
              '}':_ -> True
              _ -> False
    in case lines of
         [] -> []
         ("":l:ls) -> (if avoidSemi l then "" else ";") : layout (l:ls)
         (l:ls) -> l : layout ls

parse = Parsec.parse exp "" . unlines . layout . lines <=<
        Parsec.parse decomment ""

go = fmap run . parse
