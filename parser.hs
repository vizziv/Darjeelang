{-# LANGUAGE NoMonomorphismRestriction #-}

module Parser where

import Prelude hiding (exp)
import Control.Applicative
import qualified Data.Map as M
import qualified Data.Set as S
import Text.Parsec hiding ((<|>), optional)
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
                      P.reservedNames = ["let", "type", "branch", "zero",
                                         "nonzero", "Int"],
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
  args <- M.fromList <$>
          (braces . commaSep) ((,) <$> typ <* colon <*> identifier)
  reservedOp "="
  body <- exp
  return (TFun (M.keysSet args) result, var, E $ EFun args body)

exp = buildExpressionParser ops term

term = (parens exp <|>) . (E <$>) $ choice
       [EPrim <$> natural,
        try $ ETag <$> identifier <* reservedOp "~" <*> term,
        try $ ETag <$> identifier <* reservedOp "~!" <*> (E . EUntag <$> term),
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
        EDatas <$ reserved "type" <*> (braces . ((optional semi) *>) . semiSep)
                   ((,) <$> identifier <*
                    reservedOp "=" <* reservedOp "@" <*> typs) <*
                  reserved "in" <*> exp]

-- TODO: finish this.
layout keyword =
    let untilKeyword = (,) <$>
                       (manyTill anyToken . try . choice . map reserved $
                        ["let", "type"]) <*>
                       getInput
        f (Just indent, acc) line =
            if all (==' ') $ take indent line
            then (Just indent, (';':line):acc)
            else (Nothing, ('}':line):acc)
        f (Nothing, acc) line =
            case parse untilKeyword "" line of
              Left _ -> (Nothing, line:acc)
              -- TODO: make this way more flexible.
              Right (xs, []) -> (Just (1 + length xs), line:acc)
    in unlines . reverse . snd . foldl f (Nothing, []) . lines
