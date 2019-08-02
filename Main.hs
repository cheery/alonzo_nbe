module Main where

import Control.Monad.State.Lazy (State, runState, evalState, get, put)
import GHC.Base (Alternative, empty, (<|>))
import Data.List (elemIndex, filter, intercalate)
import qualified Data.Map as Map
import qualified Data.Set as Set
import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure)

data Term =
    Var Int
  | App Term Term
  | Abs Term
  | Name String
  | Ann Term Type
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
eval f p (Ann body ty) = eval f p body

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
references (Ann t ty) = references t

opens n = map (NVar . (n-)) [0..n-1]

-- Printing
type PrettyState a = State (Int, [String], ([Block] -> [Block])) a

page_width = 80

stringify :: Int -> (String -> Bool) -> Term -> String
stringify count occur e = pretty_init_layout margin (ss []) where
    ((), (margin, _, ss)) = runState (stringify_ 0 ctx e) (page_width, mm, id)
    ctx = reverse $ take count nn
    mm = drop count nn
    nn = fresh_names occur

stringify_ :: Int -> [String] -> Term -> PrettyState ()
stringify_ rbp ctx (Var i) = textb (ctx!!i)
stringify_ rbp ctx (Name n) = textb (lexeme (Identifier n))
stringify_ rbp ctx (App a b) = do
    leftb
    (parens_wrap rbp 10 $ do
        stringify_ 10 ctx a >> blankb " " 2 >> stringify_ 11 ctx b)
    rightb
stringify_ rbp ctx (Abs a) = do
    leftb
    (parens_wrap rbp 0 $ do
        n <- fresh_name
        textb n >> textb " " >> textb (lexeme Maple) >> blankb " " 2
        stringify_ 0 (n:ctx) a)
    rightb
stringify_ rbp ctx (Ann a ty) = do
    leftb
    stringify_ 10 ctx a
    textb " : "
    parens_wrap rbp 5 (ty_stringify_ ty)
    rightb

ty_stringify :: Type -> String
ty_stringify ty = pretty_init_layout margin (ss []) where
    ((), (margin, nn, ss)) = runState (ty_stringify_ ty) (page_width, [], id)

ty_stringify_ :: Type -> PrettyState ()
ty_stringify_ (Arrow (Arrow a b) c) = do
    leftb >> textb "(" >> ty_stringify_ (Arrow a b) >> textb ")"
    blankb " " 2 >> textb (lexeme ArrowSym) >> textb " " >> ty_stringify_ c
ty_stringify_ (Arrow (Some a) c) = do
    textb a >> textb " " >> textb (lexeme ArrowSym) >> textb " " >> ty_stringify_ c
ty_stringify_ (Some a) = textb a

parens_wrap rbp c s = if rbp <= c then s else 
    leftb >> textb "(" >> s >> textb ")" >> rightb

fresh_names :: (String -> Bool) -> [String]
fresh_names occurs = filter (not.occurs) names where
    names = [replicate k ['a'..'z'] | k <- [1..]] >>= sequence

fresh_name :: PrettyState String
fresh_name = do
    (margin, nn, s) <- get
    put (margin, tail nn, s)
    return (head nn)

insb :: (Int -> [Block] -> [Block]) -> PrettyState ()
insb node = do
    (margin, nn, s) <- get
    put (margin, nn, s.(node margin))

leftb = insb scan_left
rightb = insb scan_right
blankb text indent = insb (scan_blank text indent)
textb text = insb (scan_text text)

-- Scanner and printer internals
--
-- The scanner runs three line widths before the printer and checks how many
-- spaces the blanks and groups take. This allows the printer determine
-- whether the line or grouping should be broken into multiple lines.
scan_left margin rest = LeftB (scan_to_right 0 0 margin rest) : rest
scan_right margin rest = RightB : rest
scan_blank text indent margin rest =
    BlankB text (length text) indent (scan_to_blank 0 margin rest) : rest

scan_text :: String -> Int -> [Block] -> [Block]
scan_text text margin rest = TextB text (length text) : rest

scan_to_blank :: Int -> Int -> [Block] -> Int
scan_to_blank total margin _ | margin < total    = total
scan_to_blank total margin (BlankB _ _ _ _:rest) = total
scan_to_blank total margin (a:rest) =
    scan_to_blank (total + block_len a) margin rest
scan_to_blank total margin [] = total

scan_to_right :: Int -> Int -> Int -> [Block] -> Int
scan_to_right 0 total margin _ | margin < total = total
scan_to_right 0 total margin (RightB:rest) = total
scan_to_right n total margin (LeftB _:rest) =
    scan_to_right (n+1) total margin rest
scan_to_right n total margin (RightB:rest) =
    scan_to_right (n-1) total margin rest
scan_to_right n total margin (BlankB _ len _ _:rest) =
    scan_to_right n (total+len) margin rest
scan_to_right n total margin (TextB _ len:rest) =
    scan_to_right n (total+len) margin rest
scan_to_right n total margin [] = total

-- Layout: spaces, spaces, force_break
-- Left size, Right, Blank text len indent size, Context text len
data Block = LeftB Int | RightB | BlankB String Int Int Int | TextB String Int
block_len (LeftB _)          = 0
block_len (RightB)           = 0
block_len (BlankB _ len _ _) = len
block_len (TextB  _ len)     = len

-- Printer keeps the track of layout during printing.
data Layout = Layout Layout Int Bool

pretty_init_layout width =
    pretty_layout width width width (Layout undefined width False)

pretty_layout :: Int -> Int -> Int -> Layout -> [Block] -> String
pretty_layout margin spaceleft spaces layout (cell:cells) = case cell of
    LeftB size ->
        let layout' = Layout layout spaces (size < 0 || spaceleft < size) in
        pretty_layout margin spaceleft spaces layout' cells
    RightB ->
        let Layout layout' _ _ = layout in
        pretty_layout margin spaceleft spaces layout' cells
    BlankB text len indent size ->
        let Layout parent layout_spaces force_break = layout in
        if size < 0 || spaceleft < size || force_break
        then
            let spaces' = layout_spaces - indent
                spaceleft' = spaces' in
            ('\n' : [' ' | _ <- [spaces'..margin-1]])
            ++ pretty_layout margin spaceleft' spaces' layout cells
        else
            let len = length text in
            text ++ pretty_layout margin (spaceleft - len) spaces layout cells
    TextB text len ->
        text ++ pretty_layout margin (spaceleft - len) spaces layout cells
pretty_layout margin spaceleft spaces layout [] = []

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
    get_judgements :: Map.Map String Type,
    get_unchecked :: [String],
    get_checked :: [String] }

empty_module :: Module
empty_module = Module [] (Map.empty) (Map.empty) [] []

insert_declaration :: String -> Term -> Module -> Module
insert_declaration name term m = m {
    get_structure = (Declaration name:get_structure m),
    get_declarations = (Map.insert name term (get_declarations m)),
    get_unchecked = (name:get_unchecked m) }

insert_judgement :: String -> Type -> Module -> Module
insert_judgement name ty m = m {
    get_structure = (Judgement name:get_structure m),
    get_judgements = (Map.insert name ty (get_judgements m)),
    get_unchecked = (name:get_unchecked m) }

insert_noparse :: [Token] -> Module -> Module
insert_noparse tokens m = m {
    get_structure = (NoParse tokens:get_structure m) }

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

left_denotation ctx val = do
    accept (Colon==)
    fmap (Ann val) parse_type
    <|> do
    fmap (App val) (parse_term ctx 21)

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

data Fail =
    Untyped String
  | Undeclared
  | NotEqual Term Type Type
  | NotArrow Term Type
  | ShouldBeAnnotated Term
    deriving (Show)

verify_all :: (Module, [Fail]) -> [String] -> (Module, [Fail])
verify_all (m,es) (name:names) = case verify name m of
    Right m2 -> verify_all (m2, es) names
    Left Undeclared -> verify_all (m,es) names
    Left e   -> verify_all (m,e:es) names
verify_all (m,es) [] = (m,es)

verify :: String -> Module -> Either Fail Module
verify name m | elem name (get_checked m) = Right m
verify name m | elem name (get_unchecked m) = do
    let m2 = m { get_unchecked = filter (/=name) (get_unchecked m) }
    let decls = get_declarations m2
    let judgs = get_judgements m2
    case (Map.lookup name decls, Map.lookup name judgs) of
        (Just term, Nothing) -> Left (Untyped name)
        (Nothing,   Just ty) -> Right ()
        (Just term, Just ty) -> check m2 [] term ty
    Right $ m2 { get_checked = name : get_checked m2 }
verify name m = Left Undeclared

infer :: Module -> [Type] -> Term -> Either Fail Type
infer m ctx (Var x) = Right (ctx !! x)
infer m ctx (Name name) = do
    let judgs = get_judgements m
    case Map.lookup name judgs of
        Just ty -> Right ty
        Nothing -> Left (Untyped name)
infer m ctx (App f x) = do
    (a, b) <- infer m ctx f >>= check_arrow f
    check m ctx x a
    return b
infer m ctx (Ann t ty) = do
    check m ctx t ty
    return ty
infer m ctx oth = do
    Left (ShouldBeAnnotated oth)

check :: Module -> [Type] -> Term -> Type -> Either Fail ()
check m ctx (Abs body) ty = do
    (a,b) <- check_arrow (Abs body) ty
    check m (a:ctx) body b
check m ctx neu        ty = do
    t <- infer m ctx neu
    if ty == t then Right () else Left (NotEqual neu t ty)
    
check_arrow t (Arrow a b) = Right (a,b)
check_arrow t a = Left (NotArrow t a)

normalize_and_print :: Module -> Structure -> IO () 
normalize_and_print m (Declaration name) = do
    let decls = get_declarations m
    let judgs = get_judgements m
    let (Just term) = Map.lookup name decls
    let ref = references term
    mapM_ (report_missing_judgement judgs) ref 
    let (m2,errors) = verify_all (m,[]) (name:Set.elems ref)
    let lookup_fn x = if elem x (get_checked m2)
        then Map.lookup x decls else Nothing
    let occur name = Set.member name ref || Map.member name decls
    mapM_ (putStrLn.("# "++).error_report occur) errors
    if elem name (get_checked m2) then do
        let nterm = readback 0 (eval lookup_fn  (opens 0) term)
        putStrLn (name ++ " = " ++ stringify 0 occur nterm)
    else do
        putStrLn (name ++ " = " ++ stringify 0 occur term)
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

error_report occur (Untyped name) = name ++ " : ?"
error_report occur (ShouldBeAnnotated term) = stringify 0 occur term ++ " : ?"
error_report occur fail = show fail

report_missing_judgement judgs name =
    if Map.member name judgs
        then return ()
        else putStrLn ("# " ++ name ++ " : ?")

report_missing_declaration decls name =
    if Map.member name decls
        then return ()
        else putStrLn ("# " ++ name ++ " = ?")
