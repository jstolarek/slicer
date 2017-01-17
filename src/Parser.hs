{-# LANGUAGE ViewPatterns, ScopedTypeVariables #-}

module Parser
    ( -- * Parsing programs represented as strings
      parseIn, parseRepl

      -- * Language keywords.  Used for resugaring
    , strBool, strCase, strCaseClauseSep, strData, strElse, strFalse, strFst
    , strFun, strFunBodySep, strHole, strIf,  strIn, strInL, strInR, strInt
    , strLet, strOf, strRoll, strSnd, strString, strThen, strTrue, strUnit
    , strUnitVal
    ) where

import           Absyn
import           Env
import           Primitives
import           UpperSemiLattice

import           Prelude hiding ( exp     )
import           Control.Monad  ( liftM   )
import           Data.Char      ( isUpper )
import qualified Data.Map as Map

import           Text.ParserCombinators.Parsec hiding (Parser)
import           Text.ParserCombinators.Parsec.Language
import           Text.ParserCombinators.Parsec.Token
import           Text.ParserCombinators.Parsec.Expr


-- | Which parsing mode are we in: Compiler or Repl? The two differ in the form
-- of let statements
data ParserMode = Compiler | Repl deriving (Eq)

type ParserState = (TyCtx, ParserMode)

type Parser a = CharParser ParserState a

-- Parse a string in a type context and the empty variable context.
parseIn :: String -> TyCtx -> (TyCtx, Exp)
parseIn source tyctx =
   case runParser program (tyctx, Compiler) "" source of
      Right ((tyctx', _), e) -> (tyctx', e)
      Left err               -> error $ "Syntax error: " ++ show err

-- Parse a repl line in a type context and the empty variable context.
parseRepl :: String -> TyCtx -> Either ParseError (TyCtx, Maybe Exp)
parseRepl line tyctx =
    case runParser repl (tyctx, Repl) "" line of
      Right ((tyctx', _), e) -> Right (tyctx', e)
      Left err               -> Left err

isCompilerMode :: Parser Bool
isCompilerMode = do
  (_, mode) <- getState
  return (mode == Compiler)

-- Some constants for keywords, etc.  Note that strings tokens for operators and
-- other builtin primitives are defined in the Show instance for the Primitive
-- data type
strBool, strCase, strCaseClauseSep, strData, strElse, strFalse, strFst, strFun,
      strFunBodySep, strHole, strIf, strIn, strInL, strInR, strInt, strLet,
      strOf, strRoll, strSnd, strString, strThen, strTrace, strTrue, strUnit,
      strUnitVal, strUnroll :: String
strBool          = "bool"
strCase          = "case"
strCaseClauseSep = "->" -- separate case clause from constructor pattern
strData          = "data"
strElse          = "else"
strFalse         = "false"
strFst           = "fst"
strFun           = "fun"
strFunBodySep    = "=>"
strHole          = "_"
strIf            = "if"
strIn            = "in"
strInL           = "inl"
strInR           = "inr"
strInt           = "int"
strLet           = "let"
strOf            = "of"
strRoll          = "roll"
strSnd           = "snd"
strString        = "string"
strThen          = "then"
strTrace         = "trace"
strTrue          = "true"
strUnit          = "unit"
strUnitVal       = "()"
strUnroll        = "unroll"

-- We don't allow explicit rolls, unrolls, inls or inrs in the concrete syntax,
-- but we still reserve them as keywords.
keywords :: [String]
keywords = [ strBool, strCase, strData, strElse, strFalse, strFst, strFun
           , strIf, strIn, strInL, strInR, strInt, strLet, strOf, strRoll
           , strSnd, strThen, strTrace, strTrue, strUnit, strUnroll ] ++
  map show [ PrimVal, PrimSlice, PrimPSlice, PrimVisualize, PrimVisualize2
           , PrimProfile, PrimProfile2, PrimTreeSize, PrimWhere, PrimDep
           , PrimExpr
           ]

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
equals = reservedOp token_ (show OpEq)

typeAnnotation :: Parser Type
typeAnnotation = colon token_ >> type_

-- Use Haskell tokeniser, but reserve our own keywords
token_ :: TokenParser a
token_ = makeTokenParser haskellDef { reservedNames = keywords }

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
exp :: Parser Exp
exp =
   flip buildExpressionParser appChain
      -- each element of the _outermost_ list corresponds to a precedence level
      -- (highest first).
      [ [ Infix  (binaryOp OpMod  ) AssocLeft
        , Infix  (binaryOp OpTimes) AssocLeft
        , Infix  (binaryOp OpDiv  ) AssocLeft  ]
      , [ Infix  (binaryOp OpMinus) AssocLeft
        , Infix  (binaryOp OpPlus ) AssocLeft  ]
      , [ Infix  (binaryOp OpEq   ) AssocRight
        , Infix  (binaryOp OpLt   ) AssocRight
        , Infix  (binaryOp OpGt   ) AssocRight
        , Infix  (binaryOp OpNeq  ) AssocRight
        , Infix  (binaryOp OpLeq  ) AssocRight
        , Infix  (binaryOp OpGeq  ) AssocRight
        ]
      , [ Infix  (binaryOp OpAnd  ) AssocLeft  ]
      , [ Infix  (binaryOp OpOr   ) AssocLeft  ]
      , [ Prefix (unaryOp  OpNot  )            ]
      ]

appChain :: Parser Exp
appChain = chainl1 simpleExp (return App)

-- Expressions common to compiler and REPL: everything except different forms of
-- let-bindings. lp stands for "let parser"
simpleExp :: Parser Exp
simpleExp =
   unitVal <|> try int <|> string_ <|> true <|> false <|> if_ <|> try ctr <|>
   try var <|> fun <|> try (parenthesise exp) <|> let_ <|> pair <|> fst_ <|>
   snd_ <|> case_ <|> hole <|> trace_ <|> slice_ <|> pslice_ <|>
   traceval_ <|> visualize <|> visualize2 <|>
   profile_ <|> profile2_ <|> treesize_ <|> where_ <|> dep_ <|> expr_

unaryOp :: Primitive -> Parser (Exp -> Exp)
unaryOp op =
   reservedOp token_ (show op) >>
   (return $ \e1 -> (Op op [e1]))

binaryOp :: Primitive -> Parser (Exp -> Exp -> Exp)
binaryOp op =
   reservedOp token_ (show op) >>
   (return $ \e1 e2 -> (Op op [e1, e2]))

hole :: Parser Exp
hole = symbol token_ strHole >> typeAnnotation >>= (return . Hole)

unitVal :: Parser Exp
unitVal = reservedOp token_ strUnitVal >> return Unit

var :: Parser Exp
var = Var `liftM` var_

ctr :: Parser Exp
ctr = do c <- constr
         e <- option Unit (exp)
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

fun :: Parser Exp
fun = do
   f <- keyword strFun >> var_
   params :: [(Var,Type)] <- many1 $ parenthesise (do v  <- var_
                                                      ty <- typeAnnotation
                                                      return (v, ty))
   tau <- typeAnnotation
   reservedOp token_ strFunBodySep
   e <- exp
   return (Fun (Rec f params tau e (Just (show f))))

if_ :: Parser Exp
if_ = do
   e  <- keyword strIf   >> exp
   e1 <- keyword strThen >> exp
   e2 <- keyword strElse >> exp
   return (If e e1 e2)

let_ :: Parser Exp
let_ = do
   isCompiler <- isCompilerMode
   if isCompiler
   then letC_
   else letR_

-- let binding used in a compiler mode
letC_ :: Parser Exp
letC_ = do
   x  <- keyword strLet >> var_
   e1 <- equals         >> exp
   e2 <- keyword strIn  >> exp
   return (Let x e1 e2)

-- let binding used in a REPL mode
letR_ :: Parser Exp
letR_ = do
   x <- keyword strLet >> var_
   e <- equals         >> exp
   return (LetR x e)


pair :: Parser Exp
pair = parenthesise $ do
   e1 <- exp
   _  <- comma token_
   e2 <- exp
   return (Pair e1 e2)

fst_ :: Parser Exp
fst_ = do
   e <- keyword strFst >> exp
   return (Fst e)

snd_ :: Parser Exp
snd_ = do
   e <- keyword strSnd >> exp
   return (Snd e)

case_ :: Parser Exp
case_ = do
  keyword strCase
  e <- exp
  keyword strOf
  m <- matches
  return (Case e m)

matches :: Parser Match
matches = (Match . Map.fromList) `liftM` semiSep token_ match
    where match :: Parser (Con,([Var],Exp)) =
                   do c  <- constr
                      vs <- option [bot]  -- TODO: Empty list for nullary ctors
                            ((pure `liftM` var_) -- construct singleton list
                             <|> parenthesise (commaSep token_ var_))
                      reservedOp token_ strCaseClauseSep
                      e <- exp
                      return (c, (vs, e))

typeDef :: Parser (TyVar, TyDecl)
typeDef = do
   alpha <- keyword strData >> tyVar
   equals
   -- Assume all datatypes are binary for now :-/
   (con1, ty1) <- constrDef
   (con2, ty2) <- symbol token_ "|" >> constrDef
   let decl = TyDecl alpha [(con1, ty1), (con2, ty2)]
   updateState (\(tyctx, mode) -> (addTyDecl tyctx decl, mode))
   return (alpha, decl) -- TODO: generalize
   where
      constrDef :: Parser (Con, Type)
      constrDef = do
         c   <- constr
         tau <- option UnitTy type_
         return (c, tau)

trace_ :: Parser Exp
trace_ = do
   e <- keyword strTrace >> exp
   return (Trace e)

profile_ :: Parser Exp
profile_ = do
   e <- keyword (show PrimProfile) >> exp
   return (Op PrimProfile [e])

treesize_ :: Parser Exp
treesize_ = do
   e <- keyword (show PrimTreeSize) >> exp
   return (Op PrimTreeSize [e])

where_ :: Parser Exp
where_ = do
   e <- keyword (show PrimWhere) >> exp
   return (Op PrimWhere [e])

dep_ :: Parser Exp
dep_ = do
   e <- keyword (show PrimDep) >> exp
   return (Op PrimDep [e])

expr_ :: Parser Exp
expr_ = do
   e <- keyword (show PrimExpr) >> exp
   return (Op PrimExpr [e])

profile2_ :: Parser Exp
profile2_ = do
   e <- keyword (show PrimProfile2) >> exp
   return (Op PrimProfile2 [e])

visualize :: Parser Exp
visualize = do
   keyword (show PrimVisualize)
   parenthesise $ do e1 <- exp
                     _  <- comma token_
                     e2 <- exp
                     return (Op PrimVisualize [e1, e2])

visualize2 :: Parser Exp
visualize2 = do
   keyword (show PrimVisualize2)
   parenthesise $ do e  <- exp
                     _  <- comma token_
                     e1 <- exp
                     _  <- comma token_
                     e2 <- exp
                     return (Op PrimVisualize2 [e, e1, e2])

traceval_ :: Parser Exp
traceval_ = do
   e <- keyword (show PrimVal) >> exp
   return (Op PrimVal [e])

slice_ :: Parser Exp
slice_ = do keyword (show PrimSlice)
            (e1,e2) <- parenthesise $ do
                          e1 <- exp
                          _  <- comma token_
                          e2 <- exp
                          return (e1,e2)
            return (Op PrimSlice [e1,e2])


pslice_ :: Parser Exp
pslice_ = do keyword (show PrimPSlice)
             (e1,e2) <-  parenthesise $ do
                            e1 <- exp
                            _  <- comma token_
                            e2 <- exp
                            return (e1,e2)
             return (Op PrimPSlice [e1,e2])

-- In REPL mode we either parse a data definition or an expression
repl :: Parser (ParserState, Maybe Exp)
repl =
  (typeDef >> getState >>= (\s -> return (s, Nothing))) <|>
  (do e <- exp
      s <- getState
      return (s, Just e))

-- A type context, a variable context in that type context, and then an
-- expression in that variable context.
program :: Parser (ParserState, Exp)
program = do
   _      <- many typeDef -- discards type ctxt, we'll read it from parser state
   e      <- exp
   eof
   tyCtx' <- getState
   return (tyCtx', e)
