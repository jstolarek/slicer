{-# LANGUAGE ViewPatterns, ScopedTypeVariables #-}

module UntypedParser
    ( -- * Parsing programs represented as strings
      parseIn, parseRepl

      -- * Language keywords.  Used for resugaring
    , strAnd, strBool, strCase, strCaseClauseSep, strData, strDiv, strElse
    , strEq,  strFalse, strFst, strFun, strFunBodySep, strGeq, strGt, strHole
    , strIf,  strIn, strInL, strInR, strInt, strLeq, strLet, strLt, strMinus
    , strMod, strNeq, strNot, strOf, strOr, strPlus, strRoll, strSnd, strString
    , strThen, strTimes, strTrue, strUnit, strUnitVal, strUnroll
    , strWith
    ) where

import           Prelude hiding ( exp     )
import           Control.Monad  ( liftM   )
import           Data.Char      ( isUpper )
import           Data.Function  ( fix     )
import qualified Data.Map as Map

import           Text.ParserCombinators.Parsec hiding (Parser)
import           Text.ParserCombinators.Parsec.Language
import           Text.ParserCombinators.Parsec.Token
import           Text.ParserCombinators.Parsec.Expr

import           Absyn hiding   ( ty )
import           Env
import           UpperSemiLattice


-- Some constants for keywords, etc.
strAnd, strBool, strCase, strCaseClauseSep, strData, strDiv, strElse, strEq,
      strFalse, strFst, strFun, strFunBodySep, strGeq, strGt, strHole, strIf,
      strIn, strInL, strInR, strInt, strLeq, strLet, strLt, strMinus, strMod,
      strNeq, strNot, strOf, strOr, strPlus, strRoll, strSnd, strString,
      strThen, strTimes, strTrue, strUnit, strUnitVal, strUnroll,
      strWith :: String
strAnd           = "&&"
strBool          = "bool"
strCase          = "case"
strCaseClauseSep = "->" -- separate case clause from constructor pattern
strData          = "data"
strDiv           = "/"
strElse          = "else"
strEq            = "="
strFalse         = "false"
strFst           = "fst"
strFun           = "fun"
strFunBodySep    = "=>"
strGeq           = ">="
strGt            = ">"
strHole          = "_"
strIf            = "if"
strIn            = "in"
strInL           = "inl"
strInR           = "inr"
strInt           = "int"
strLeq           = "<="
strLet           = "let"
strLt            = "<"
strMinus         = "-"
strMod           = "%"
strNeq           = "/="
strNot           = "not"
strOf            = "of"
strOr            = "||"
strPlus          = "+"
strRoll          = "roll"
strSnd           = "snd"
strString        = "string"
strThen          = "then"
strTimes         = "*"
strTrue          = "true"
strUnit          = "unit"
strUnitVal       = "()"
strUnroll        = "unroll"
strWith          = "with"

strAs, strDep, strExpr, strPSlice, strProfile, strProfile2, strReplay, strSlice,
     strTrace, strTreesize, strUpdate, strVal, strVar, strVisualize,
     strVisualize2, strWhere :: String
strAs         = "as"
strDep        = "dep"
strExpr       = "expr"
strPSlice     = "pslice"
strProfile    = "profile"
strProfile2   = "profile2"
strReplay     = "replay"
strSlice      = "slice"
strTrace      = "trace"
strTreesize   = "treesize"
strUpdate     = "update"
strVal        = "read"
strVar        = "var"
strVisualize  = "visualize"
strVisualize2 = "visualize2"
strWhere      = "where"

-- We don't allow explicit rolls, unrolls, inls or inrs in the concrete syntax,
-- but we still reserve them as keywords.
keywords :: [String]
keywords = [ strBool, strCase, strData, strElse, strFalse, strFst, strFun
           , strIf, strIn, strInL, strInR, strInt, strLet, strOf, strRoll
           , strSnd, strThen, strTrue, strUnit, strUnroll, strWith, strTrace
           , strVal, strReplay, strSlice, strPSlice, strAs, strVar, strUpdate
           , strVisualize, strVisualize2, strProfile, strTreesize,strProfile2
           , strWhere, strDep, strExpr]

operators :: [String]
operators = [ strMod, strTimes, strDiv, strMinus, strPlus, strEq, strLt, strGt
            , strNeq, strLeq, strGeq, strAnd, strOr, strNot ]

-- Parse a string in a type context and the empty variable context.
parseIn :: String -> TyCtx -> (TyCtx, Exp)
parseIn source tyctx =
   case runParser program tyctx "" source of
      Left err          -> error $ "Syntax error: " ++ show err
      Right (tyctx', e) -> (tyctx', e)

-- Parse a repl line in a type context and the empty variable context.
parseRepl :: String -> TyCtx -> Either ParseError (TyCtx, Maybe Exp)
parseRepl line tyctx = runParser repl tyctx "" line

type Parser a = CharParser TyCtx a

-- Some helpers.
parenthesise :: CharParser st a -> CharParser st a
parenthesise = parens token_

keyword :: String -> CharParser st ()
keyword = reserved token_

-- variables start with lower case or underscore
var_ :: CharParser st Var
var_ = V `liftM` identifier token_

-- constructors start with upper case
constr :: CharParser st Con
constr = do t@(a:_) <- identifier token_
            if isUpper a
            then return (C t)
            else pzero

tyVar :: CharParser st TyVar
tyVar = TV `liftM` identifier token_

equals :: CharParser st ()
equals = reservedOp token_ strEq

typeAnnotation :: Parser Type
typeAnnotation = colon token_ >> type_

-- Use Haskell tokeniser, but reserve our own keywords
token_ :: TokenParser a
token_ = makeTokenParser haskellDef { reservedNames   = keywords
                                    , reservedOpNames = operators }

type_ :: Parser Type
type_ = flip buildExpressionParser simpleType
      -- each element of the _outermost_ list corresponds to a precedence level
      -- (highest first).
      [ [ Infix (typeOp "*"  (PairTy)) AssocLeft
        , Infix (typeOp "+"  (SumTy )) AssocLeft  ]
      , [ Infix (typeOp "->" (FunTy )) AssocRight ]
      ]

context :: Parser Ctx
context = do xas <- commaSep token_ $ do
                      x   <- var_
                      tau <- typeAnnotation
                      return (x, tau)
             return $ Env (Map.fromList xas)

-- We don't allow direct use of recursive types in the concrete grammar.
simpleType :: Parser Type
simpleType = boolTy <|> intTy <|> stringTy <|> unitTy <|> typeVar <|> traceType
         <|> parensType
   where
      intTy :: CharParser st Type
      intTy = keyword strInt >> return IntTy

      stringTy :: CharParser st Type
      stringTy = keyword strString >> return StringTy

      boolTy :: CharParser st Type
      boolTy = keyword strBool >> return BoolTy

      unitTy :: CharParser st Type
      unitTy = keyword strUnit >> return UnitTy

      typeVar :: CharParser st Type
      typeVar = tyVar >>= return . TyVar

      traceType = do keyword strTrace
                     ctx <- parenthesise context
                     ty  <- simpleType
                     return (TraceTy ctx ty)

      parensType :: Parser Type
      parensType = parenthesise type_

typeOp :: String -> (Type -> Type -> Type) -> CharParser st (Type -> Type -> Type)
typeOp str op = reservedOp token_ str >> return op

-- An exp is an operator tree. An operator tree is a tree whose branches are
-- binary primitives and whose leaves are application chains. An application
-- chain is a left-associative tree of simple exps. A simple exp is any exp
-- other than an operator tree or an application chain.
exp :: Parser Exp -> Parser Exp
exp lp =
   flip buildExpressionParser (appChain lp)
      -- each element of the _outermost_ list corresponds to a precedence level
      -- (highest first).
      [ [ Infix  (binaryOp strMod   opMod   ) AssocLeft
        , Infix  (binaryOp strTimes opTimes ) AssocLeft
        , Infix  (binaryOp strDiv   opDiv   ) AssocLeft  ]
      , [ Infix  (binaryOp strMinus opMinus ) AssocLeft
        , Infix  (binaryOp strPlus  opPlus  ) AssocLeft  ]
      , [ Infix  (binaryOp strEq    opIntEq ) AssocRight
        , Infix  (binaryOp strLt    opLt    ) AssocRight
        , Infix  (binaryOp strGt    opGt    ) AssocRight
        , Infix  (binaryOp strNeq   opIntNeq) AssocRight
        , Infix  (binaryOp strLeq   opLeq   ) AssocRight
        , Infix  (binaryOp strGeq   opGeq   ) AssocRight
        ]
      , [ Infix  (binaryOp strAnd   opAnd   ) AssocLeft  ]
      , [ Infix  (binaryOp strOr    opOr    ) AssocLeft  ]
      , [ Prefix (unaryOp  strNot   opNot   )            ]
      ]

appChain :: Parser Exp -> Parser Exp
appChain lp = chainl1 (simpleExp lp) (return App)

-- Expressions common to compiler and REPL: everything except different forms of
-- let-bindings. lp stands for "let parser"
simpleExp :: Parser Exp -> Parser Exp
simpleExp lp =
   unitVal <|> try int <|> string_ <|> true <|> false <|> if_ lp <|>
   try (ctr lp) <|> try var <|> fun lp <|> try (parenthesise (exp lp)) <|>
   lp <|> pair lp <|> fst_ lp <|> snd_ lp <|> case_ lp <|> hole <|>
   trace_ lp <|> replay_ lp <|> slice_ lp <|> pslice_ lp <|> traceval_ lp <|>
   tracevar_ lp <|> traceupd_ lp <|> visualize lp <|> visualize2 lp <|>
   profile_ lp <|> profile2_ lp <|> treesize_ lp <|> where_ lp <|> dep_ lp <|>
   expr_ lp

unaryOp :: String -> Op -> Parser (Exp -> Exp)
unaryOp str op =
   reservedOp token_ str >>
   (return $ \e1 -> (Op op [e1]))

binaryOp :: String -> Op -> Parser (Exp -> Exp -> Exp)
binaryOp str op =
   reservedOp token_ str >>
   (return $ \e1 e2 -> (Op op [e1, e2]))

hole :: Parser Exp
hole = symbol token_ strHole >> typeAnnotation >>= (return . Hole)

unitVal :: Parser Exp
unitVal = reservedOp token_ strUnitVal >> return Unit

var :: Parser Exp
var = Var `liftM` var_

ctr :: Parser Exp -> Parser Exp
ctr lp = do c <- constr
            e <- option Unit (exp lp)
            return (Con c [e])

int :: Parser Exp
int = (CInt . fromIntegral) `liftM` natural token_ <|>
      (parenthesise (char '-' >> (CInt . negate . fromIntegral) `liftM` natural token_))

string_ :: Parser Exp
string_ = CString `liftM` stringLiteral token_

true :: Parser Exp
true = keyword strTrue >> return (CBool True)

false :: Parser Exp
false = keyword strFalse >> return (CBool False)

fun :: Parser Exp -> Parser Exp
fun lp = do
   f <- keyword strFun >> var_
   params :: [(Var,Type)] <- many1 $ parenthesise (do v  <- var_
                                                      ty <- typeAnnotation
                                                      return (v, ty))
   tau <- option Nothing (Just `liftM` typeAnnotation)
   reservedOp token_ strFunBodySep
   e <- exp lp
   return (Fun (Rec f params tau e (Just (show f))))

if_ :: Parser Exp -> Parser Exp
if_ lp = do
   e  <- keyword strIf   >> exp lp
   e1 <- keyword strThen >> exp lp
   e2 <- keyword strElse >> exp lp
   return (If e e1 e2)

let_ :: Parser Exp -> Parser Exp
let_ lp = do
   x  <- keyword strLet >> var_
   e1 <- equals         >> exp lp
   e2 <- keyword strIn  >> exp lp
   return (Let x e1 e2)

-- let binding used in a REPL
letR_ :: Parser Exp -> Parser Exp
letR_ lp = do
   x <- keyword strLet >> var_
   e <- equals         >> exp lp
   return (LetR x e)


pair :: Parser Exp -> Parser Exp
pair lp = parenthesise $ do
   e1 <- exp lp
   _  <- comma token_
   e2 <- exp lp
   return (Pair e1 e2)

fst_ :: Parser Exp -> Parser Exp
fst_ lp = do
   e <- keyword strFst >> exp lp
   return (Fst e)

snd_ :: Parser Exp -> Parser Exp
snd_ lp = do
   e <- keyword strSnd >> exp lp
   return (Snd e)

case_ :: Parser Exp -> Parser Exp
case_ lp = do
  keyword strCase
  e <- exp lp
  keyword strOf
  m <- matches lp
  return (Case e m)

matches :: Parser Exp -> Parser Match
matches lp = (Match . Map.fromList) `liftM` semiSep token_ match
    where match :: Parser (Con,([Var],Exp)) =
                   do c  <- constr
                      vs <- option [bot]  -- TODO: Empty list for nullary ctors
                            ((pure `liftM` var_) -- construct singleton list
                             <|> parenthesise (commaSep token_ var_))
                      reservedOp token_ strCaseClauseSep
                      e <- exp lp
                      return (c, (vs, e))

typeDef :: Parser (TyVar, TyDecl)
typeDef = do
   alpha <- keyword strData >> tyVar
   equals
   -- Assume all datatypes are binary for now :-/
   (con1, ty1) <- constrDef
   (con2, ty2) <- symbol token_ "|" >> constrDef
   let decl = TyDecl alpha [(con1,[ty1]), (con2,[ty2])]
   updateState (\tyctx -> addTyDecl tyctx decl)
   return (alpha, decl) -- TODO: generalize
   where
      constrDef :: Parser (Con, Type)
      constrDef = do
         c   <- constr
         tau <- option UnitTy type_
         return (c, tau)

trace_ :: Parser Exp -> Parser Exp
trace_ lp = do
   e <- keyword strTrace >> exp lp
   return (Trace e)

profile_ :: Parser Exp -> Parser Exp
profile_ lp = do
   e <- keyword strProfile >> exp lp
   return (Op (O "profile") [e])

treesize_ :: Parser Exp -> Parser Exp
treesize_ lp = do
   e <- keyword strTreesize >> exp lp
   return (Op (O "treesize") [e])

where_ :: Parser Exp -> Parser Exp
where_ lp = do
   e <- keyword strWhere >> exp lp
   return (Op (O "where") [e])

dep_ :: Parser Exp -> Parser Exp
dep_ lp = do
   e <- keyword strDep >> exp lp
   return (Op (O "dep") [e])

expr_ :: Parser Exp -> Parser Exp
expr_ lp = do
   e <- keyword strExpr >> exp lp
   return (Op (O "expr") [e])

profile2_ :: Parser Exp -> Parser Exp
profile2_ lp = do
   e <- keyword strProfile2 >> exp lp
   return (Op (O "profile2") [e])

visualize :: Parser Exp -> Parser Exp
visualize lp = do
   keyword strVisualize
   parenthesise $ do e1 <- exp lp
                     _  <- comma token_
                     e2 <- exp lp
                     return (Op (O "visualize") [e1, e2])

visualize2 :: Parser Exp -> Parser Exp
visualize2 lp = do
   keyword strVisualize2
   parenthesise $ do e  <- exp lp
                     _  <- comma token_
                     e1 <- exp lp
                     _  <- comma token_
                     e2 <- exp lp
                     return (Op (O "visualize2") [e, e1, e2])

traceval_ :: Parser Exp -> Parser Exp
traceval_ lp = do
   e <- keyword strVal >> exp lp
   return (Op (O "val") [e])

tracevar_ :: Parser Exp -> Parser Exp
tracevar_ lp = do
  keyword strVar
  x <- var_
  keyword strIn
  e <- exp lp
  return (TraceVar e x)

traceupd_ :: Parser Exp -> Parser Exp
traceupd_ lp = do
   keyword strUpdate
   e1 <- exp lp
   keyword strWith
   x <- var_
   keyword strAs
   e2 <- exp lp
   return (TraceUpd e1 x e2)

replay_ :: Parser Exp -> Parser Exp
replay_ lp = do
   e <- keyword strReplay >> exp lp
   return (Op (O "replay") [e])

slice_ :: Parser Exp -> Parser Exp
slice_ lp = do keyword strSlice
               (e1,e2) <- parenthesise $ do
                          e1 <- exp lp
                          _  <- comma token_
                          e2 <- exp lp
                          return (e1,e2)
               return (Op (O "slice") [e1,e2])


pslice_ :: Parser Exp -> Parser Exp
pslice_ lp = do keyword strPSlice
                (e1,e2) <-  parenthesise $ do
                            e1 <- exp lp
                            _  <- comma token_
                            e2 <- exp lp
                            return (e1,e2)
                return (Op (O "pslice") [e1,e2])

repl :: Parser (TyCtx, Maybe Exp)
repl =
  (typeDef >> getState >>= (\s -> return (s, Nothing))) <|>
  (do e <- exp (fix letR_)
      s <- getState
      return (s, Just e))

-- A type context, a variable context in that type context, and then an
-- expression in that variable context.
program :: Parser (TyCtx, Exp)
program = do
   _      <- many typeDef -- discards type ctxt, we'll read it from parser state
   e      <- exp (fix let_)
   eof
   tyCtx' <- getState
   return (tyCtx', e)
