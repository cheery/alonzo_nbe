module Main where

import GHC.Base (Alternative, empty, (<|>))
import Data.List (elemIndex, filter, intercalate)
import qualified Data.Map as Map
import qualified Data.Set as Set
import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure)

data Term = Var Int | App Term Term | Name String | Abs Term
            deriving (Show, Eq)

data Type = Some String | Arrow Type Type
            deriving (Show, Eq)

data Value =
    Closure (String -> Maybe Term) [Value] Term
  | NVar Int
  | NName String
  | NAp Value Value

eval :: (String -> Maybe Term) -> [Value] -> Term -> Value
eval f p (Var i) = (p !! i)
eval f p (Name n) = case f n of
    Just v  -> eval f [] v
    Nothing -> NName n
eval f p (App rat ran) = apply (eval f p rat) (eval f p ran)
eval f p (Abs body) = (Closure f p body)

apply :: Value -> Value -> Value
apply (Closure f env term) arg = eval f (arg:env) term
apply p arg = NAp p arg

readback :: Int -> Value -> Term
readback k (Closure f p body) = Abs (readback (k+1) (eval f (NVar (k+1):p) body))
readback k (NVar i)           = (Var (k - i))
readback k (NName n)          = Name n
readback k (NAp rat ran)      = App (readback k rat) (readback k ran)

references :: Term -> Set.Set String
references (Var i)  = Set.empty
references (App a b) = Set.union (references a) (references b)
references (Abs a)   = references a
references (Name n)  = Set.singleton n

opens n = map (NVar . (n-)) [0..n-1]

-- Printing (not pretty for now)
stringify count occur e = fst (stringify_ 0 (drop count nn) (reverse $ take count nn) e) where
    nn = (fresh_names occur)

stringify_ :: Int -> [String] -> [String] -> Term -> (String, [String])
stringify_ rbp nn ctx (Var i) = (ctx!!i, nn)
stringify_ rbp nn ctx (Name n) = (lexeme (Identifier n), nn)
stringify_ rbp nn ctx (App a b) = 
    let (s1, nnn) = stringify_ 10 nn ctx a in
    let (s2, nnnn) = stringify_ 11 nnn ctx b in
        (parens_wrap rbp 10 (s1 ++ " " ++ s2), nnnn)
stringify_ rbp (n:nn) ctx (Abs a) = 
    let (s, nnn) = stringify_ 0 nn (n:ctx) a in
        (parens_wrap rbp 0 (n ++ " " ++ lexeme Maple ++ " " ++ s), nnn)

ty_stringify (Arrow (Arrow a b) c) =
    "(" ++ ty_stringify (Arrow a b) ++ ") "
    ++ lexeme ArrowSym ++ " " ++ ty_stringify c
ty_stringify (Arrow (Some a) c) =
    a ++ " " ++ lexeme ArrowSym ++ " " ++ ty_stringify c
ty_stringify (Some a) = a

parens_wrap rbp c s = if rbp <= c then s else "(" ++ s ++ ")"

fresh_names :: (String -> Bool) -> [String]
fresh_names occurs = filter (not.occurs) names where
    names = [replicate k ['a'..'z'] | k <- [1..]] >>= sequence

-- Parsing
newtype Parser a = Parser ([Token] -> Either [Token] (a,[Token]))

instance Functor Parser where
    fmap f (Parser p) = Parser (\s -> do
        (a, s) <- p s
        Right (f a, s))

instance Applicative Parser where
    pure a = Parser (\s -> Right (a, s))
    Parser f <*> Parser p = Parser (\s -> do
        (f,s) <- f s
        (a,s) <- p s
        Right (f a, s))

instance Monad Parser where
    return a = Parser (\s -> Right (a,s))
    Parser p >>= f  = Parser (\s -> do
        (a,s) <- p s
        let Parser p_next = f a
        p_next s)

instance Alternative Parser where
    empty = Parser (\s -> Left s)
    Parser p <|> Parser q = Parser (\s ->
        case p s of
            Right x -> Right x
            Left _ -> q s)

parse :: Parser a -> [Token] -> Either [Token] (a,[Token])
parse (Parser f) = f

accept :: (Token -> Bool) -> Parser Token
accept is_symbol = Parser casing where
    casing (a:s) | is_symbol a = Right (a,s)
    casing s                   = Left s

peek :: (Token -> Bool) -> Parser Token
peek is_symbol = Parser casing where
    casing (a:s) | is_symbol a = Right (a,a:s)
    casing s                   = Left s

at_eof :: Parser ()
at_eof = Parser casing where
    casing [] = Right ((), [])
    casing s  = Left s

data Structure =
    Declaration String
  | Judgement String
  | NoParse [Token]

data Module = Module {
    get_structure :: [Structure],
    get_declarations :: Map.Map String Term,
    get_judgements :: Map.Map String Type }

empty_module :: Module
empty_module = Module [] (Map.empty) (Map.empty)

insert_declaration :: String -> Term -> Module -> Module
insert_declaration name term m = Module
    (Declaration name:get_structure m)
    (Map.insert name term (get_declarations m))
    (get_judgements m)

insert_judgement :: String -> Type -> Module -> Module
insert_judgement name ty m = Module
    (Judgement name:get_structure m)
    (get_declarations m)
    (Map.insert name ty (get_judgements m))

insert_noparse :: [Token] -> Module -> Module
insert_noparse tokens m = Module
    (NoParse tokens:get_structure m)
    (get_declarations m)
    (get_judgements m)

parse_module  = do
    (at_eof >> return empty_module)
    <|> do
    insert <- (parse_statement <|> parse_noparse)
    do
        (at_eof >> return (insert empty_module))
        <|>
        (accept (Endline==) >> fmap insert parse_module)

parse_statement = do
    i <- accept is_identifier
    let (Identifier name) = i
    do
        accept (Equals==)
        term <- parse_term [] 0
        return (insert_declaration name term)
        <|> do
        accept (Colon==)
        ty <- parse_type
        return (insert_judgement name ty)

parse_noparse = do
    tokens <- rollto (Endline/=)
    return (insert_noparse tokens)
    where
    rollto cond = Parser (\s ->
        Right (takeWhile cond s, dropWhile cond s))

parse_type = do
    t <- do
        accept (LParen==)
        ty <- parse_type
        accept (RParen==)
        return ty
        <|> do
        i <- accept is_identifier
        let (Identifier name) = i
        return (Some name)
    do
        accept (ArrowSym==)
        fmap (Arrow t) parse_type
        <|>
        return t
    

parse_term ctx rbp = do
    accept (LParen==)
    term <- parse_term ctx 0
    accept (RParen==)
    lbp_loop ctx rbp term
    <|> do
    i <- accept is_identifier
    let (Identifier name) = i
    do
        lbp_check rbp >> accept (Maple==)
        body <- parse_term (name:ctx) 9
        lbp_loop ctx rbp (Abs body)
        <|>
        lbp_loop ctx rbp (getvar ctx name)

getvar ctx name = case elemIndex name ctx of
    Just i -> Var i
    Nothing -> Name name

lbp_loop ctx rbp item = do
    (lbp_check rbp >> left_denotation ctx item >>= lbp_loop ctx rbp)
    <|>
    return item

lbp_check rbp = peek check where
    check (LParen)       | rbp < 20 = True
    check (Identifier a) | rbp < 20 = True
    check (Equals)       | rbp < 5  = True
    check (Colon)        | rbp < 5  = True
    check (Maple)        | rbp < 30 = True
    check s              = False

left_denotation ctx fun = do
    (peek (LParen==) <|> peek is_identifier)
    fmap (App fun) (parse_term ctx 0)
    <|> do
    fmap (App fun) (parse_term ctx 20)

-- Tokenization
data Token =
      Endline
    | Whitespace
    | Garbled String
    | Identifier String
    | Maple
    | ArrowSym
    | Colon
    | Equals
    | LParen
    | RParen
    deriving (Show, Eq)

is_garbled (Garbled _) = True
is_garbled _ = False

is_identifier (Identifier _) = True
is_identifier _ = False

lexeme :: Token -> String
lexeme Endline = "\n"
lexeme Whitespace = " "
lexeme (Garbled s) = s
lexeme (Identifier s) = s
lexeme Maple = "↦"
lexeme ArrowSym = "→"
lexeme Colon = ":"
lexeme Equals = "="
lexeme LParen = "("
lexeme RParen = ")"

tokenize_all :: String -> [Token]
tokenize_all s = drop_if_endline (tokenize_all_ s) where 
    drop_if_endline (Endline:s) = s
    drop_if_endline s = s

tokenize_all_ [] = []
tokenize_all_ s  = let (t, u) = tokenize s in
    case t of
        Whitespace -> tokenize_all_ u
        t -> t:tokenize_all_ u

tokenize :: String -> (Token, String)
tokenize (a:s) | is_space a = whitespace s (a == '\n') where
    whitespace (a:s) isnl | is_space a = whitespace s (a == '\n')
    whitespace ('#':s) isnl = whitespace (dropWhile (/='\n') s) False
    whitespace [] True = (Whitespace, s)
    whitespace s True  = (Endline, s)
    whitespace s False = (Whitespace, s)
tokenize ('#':s) = (Whitespace, dropWhile (/='\n') s)
tokenize (a:s) | is_symbol a = identifier (a:) s where
    identifier p (b:s) | is_symbol b = identifier (p.(b:)) s
    identifier p (b:s) | is_num b    = identifier (p.(b:)) s
    identifier p s                   = (Identifier (p []), s)
tokenize ('↦':s) = (Maple, s)
tokenize ('→':s) = (ArrowSym, s)
tokenize (':':s) = (Colon, s)
tokenize ('=':s) = (Equals, s)
tokenize ('(':s) = (LParen, s)
tokenize (')':s) = (RParen, s)
tokenize (a:s) = (Garbled (a:[]), s)

is_space ' ' = True
is_space '\n' = True
is_space '\t' = True
is_space '\r' = True
is_space _ = False

is_symbol a | 'a' <= a && a <= 'z' = True
is_symbol a | 'A' <= a && a <= 'Z' = True
is_symbol '_' = True
is_symbol _ = False

is_num a | '0' <= a && a <= '9' = True
is_num _ = False

-- Main interface
main = do 
    args <- getArgs
    prg <- getProgName
    case args of
        [a] -> load_module a
        _ -> putStrLn $ "usage: "++prg++" module_path"

load_module path = do
    source <- readFile path
    let tokens = tokenize_all source
    case parse parse_module tokens of
        Right (m,[]) ->
            mapM_ (normalize_and_print m) (get_structure m)
        Left s -> do
            putStrLn ("parse error at token:"
                ++ (show (head s)))
            exitFailure

normalize_and_print :: Module -> Structure -> IO () 
normalize_and_print m (Declaration name) =
    let decls = get_declarations m
        judgs = get_judgements m
        (Just term) = Map.lookup name decls in do
        let nterm = readback 0 (eval (\x -> Map.lookup x decls) (opens 0) term)
        let ref = references nterm
        let occur name = Set.member name ref || Map.member name decls
        mapM_ (report_missing_judgement judgs) ref 
        putStrLn (name ++ " = " ++ stringify 0 occur nterm)
normalize_and_print m (Judgement name) = do
    let judgs = get_judgements m
    let decls = get_declarations m
    let (Just ty) = Map.lookup name judgs
    putStrLn (name ++ " : " ++ ty_stringify ty)
    report_missing_declaration decls name
normalize_and_print m (NoParse tokens) = do
    let text = intercalate " " (map lexeme tokens)
    putStrLn "# syntax error on the next line"
    putStrLn text

report_missing_judgement judgs name =
    if Map.member name judgs
        then return ()
        else putStrLn ("# " ++ name ++ " : ?")

report_missing_declaration decls name =
    if Map.member name decls
        then return ()
        else putStrLn ("# " ++ name ++ " = ?")
