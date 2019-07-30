module Main where
import Data.List (elemIndex, filter)
import Control.Applicative ((<*>))
import qualified Data.Map as Map
import qualified Data.Set as Set
import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure)

data Term = Var Int | App Term Term | Name String | Abs Term
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

parens_wrap rbp c s = if rbp <= c then s else "(" ++ s ++ ")"

fresh_names :: (String -> Bool) -> [String]
fresh_names occurs = filter (not.occurs) names where
    names = concat (map n_names [1..])
    n_names 1 = prefixes <*> [""]
    n_names n = prefixes <*> (n_names (n-1))
    prefixes = [(:)] <*> ['a'..'z']

-- Parsing
accept is_symbol (a:s) | is_symbol a = Right (a,s)
accept _ s = Left s

data Structure = Declaration String

data Module = Module {
    get_structure :: [Structure],
    get_declarations :: Map.Map String Term }

empty_module :: Module
empty_module = Module [] (Map.empty)

insert_declaration :: String -> Term -> Module -> Module
insert_declaration name term m = Module
    (Declaration name:get_structure m)
    (Map.insert name term (get_declarations m))

parse_module :: [Token] -> Either [Token] Module
parse_module [] = Right empty_module
parse_module s  = do
    (insert, s) <- parse_statement s
    case s of
      []        -> Right (insert empty_module)
      Endline:s -> fmap insert (parse_module s)
      s         -> Left s

parse_statement s = do
    (i,s) <- accept is_identifier s
    let (Identifier name) = i
    (_,s) <- accept (Equals==) s
    (term,s) <- parse_term [] 0 s
    return (insert_declaration name term, s)
 
parse_term ctx rbp s = do
    case accept (LParen==) s of
        Right (_,s) -> do
            (term,s) <- parse_term ctx 0 s
            (_,s) <- accept (RParen==) s
            lbp_loop ctx rbp (term, s)
        Left s -> do
            (i,s) <- accept is_identifier s
            let (Identifier name) = i
            case lbp_check rbp s >>= accept (Maple==) of
                Right (_,s) -> do
                    (body, s) <- parse_term (name:ctx) 9 s
                    lbp_loop ctx rbp (Abs body, s)
                Left s -> lbp_loop ctx rbp (getvar ctx name, s)

getvar ctx name = case elemIndex name ctx of
    Just i -> Var i
    Nothing -> Name name

lbp_loop ctx rbp (item, s) =
    case lbp_check rbp s of
        Right s -> do
            left_denotation ctx (item, s) >>= lbp_loop ctx rbp
        Left s -> do return (item, s)

lbp_check rbp (LParen:s)       | rbp < 20 = Right (LParen:s)
lbp_check rbp (Identifier a:s) | rbp < 20 = Right (Identifier a:s)
lbp_check rbp (Equals:s)       | rbp < 5  = Right (Equals:s)
lbp_check rbp (Maple:s)        | rbp < 30 = Right (Maple:s)
lbp_check rbp s                = Left s

left_denotation ctx (fun, LParen:s) = do
    (app,s) <- parse_term ctx 0 (LParen:s)
    return (App fun app,s)
left_denotation ctx (fun, Identifier n:s) = do
    (app,s) <- parse_term ctx 20 (Identifier n:s)
    return (App fun app,s)
left_denotation ctx (_,s) = Left s

-- Tokenization
data Token =
      Endline
    | Whitespace
    | Garbled String
    | Identifier String
    | Maple
    | Arrow
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
lexeme Arrow = "→"
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
tokenize ('→':s) = (Arrow, s)
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
    case parse_module tokens of
        Right m ->
            mapM_ (normalize_and_print m) (get_structure m)
        Left s -> do
            putStrLn ("parse error at token:"
                ++ (show (head s)))
            exitFailure

normalize_and_print :: Module -> Structure -> IO () 
normalize_and_print m (Declaration name) =
    let decls = get_declarations m
        (Just term) = Map.lookup name decls in do
        let nterm = readback 0 (eval (\x -> Map.lookup x decls) (opens 0) term)
        let ref = references nterm
        let occur name = Set.member name ref || Map.member name decls
        putStrLn (name ++ " = " ++ stringify 0 occur nterm)
