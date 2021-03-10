-- | This module defines the syntax of MiniLogo and provides some definitions
--   that are needed to define its semantics.
--
--   NOTE: You should not change the definitions in this file!
--
module MiniLogo where

import Data.List (intercalate)


--
-- * Syntax
--

-- | Variable names.
type Var = String

-- | Macro names.
type Macro = String

-- | The parameters of a macro are a list of variables that will be bound to
--   the arguments passed to the macro when it is called.
type Pars = [Var]

-- | The arguments to be evaluated and passed to a macro.
type Args = [Expr]

-- | A sequence of commands.
type Block = [Cmd]

-- | The mode of the pen.
data Mode = Down | Up
  deriving (Eq,Show)

-- | Expressions.
data Expr
   = Ref Var
   | Lit Int
   | Add Expr Expr
   | Mul Expr Expr
  deriving (Eq,Show)

-- | Commands.
data Cmd
   = Pen Mode
   | Move Expr Expr
   | Call Macro Args
   | For Var Expr Expr Block
  deriving (Eq,Show)

-- | Macro definitions.
data Def = Define Macro Pars Block
  deriving (Eq,Show)

-- | A program is a list of macro definitions plus the block of the main macro.
data Prog = Program [Def] Block
  deriving (Eq,Show)


--
-- * Environments
--

-- These definitions are used only in the semantics of MiniLogo.

-- | A generic map from keys to values.
type Map k v = [(k,v)]

-- | Lookup a value in the map.
get :: Eq k => k -> Map k v -> Maybe v
get = lookup

-- | Lookup a value in the map or fail with a runtime error if the key is not
--   in the map. Use this only when you're *positive* the entry will be in the
--   map (e.g. because you already statically checked your MiniLogo program).
getOrFail :: (Eq k, Show k) => k -> Map k v -> v
getOrFail k = maybe notFound id . get k
  where notFound = error ("key not found: " ++ show k)

-- | Add an entry to the map.
set :: k -> v -> Map k v -> Map k v
set k v m = (k,v) : m

-- | Add several new entries to the map at once. The lists of keys and values
--   should be the same length. If they're not, only as many bindings as the
--   shorter list contains will be added.
setAll :: [k] -> [v] -> Map k v -> Map k v
setAll ks vs m = zip ks vs ++ m

-- | The variable environment maps variables to integers. It is used for
--   the arguments passed to macros and the variables associated with
--   for-loops.
type Env = Map Var Int

-- | The macro environment contains the macros defined in the program. It maps
--   macro names to a pair of containing the list of parameters and the body
--   of the macro.
type Macros = Map Macro (Pars,Block)


--
-- * Pretty printing
--

-- These are helpful for debugging your MiniLogo programs.

-- | Pretty print the pen mode.
prettyMode :: Mode -> String
prettyMode Down = "down"
prettyMode Up   = "up"

-- | Pretty print an expression.
prettyExpr :: Expr -> String
prettyExpr (Ref x)   = x
prettyExpr (Lit i)   = show i
prettyExpr (Add l r) = prettyExpr l ++ " + " ++ prettyExpr r
prettyExpr (Mul l r) = prettyHelp l ++ " * " ++ prettyHelp r
  where
    prettyHelp e@(Add _ _) = "(" ++ prettyExpr e ++ ")"
    prettyHelp e           = prettyExpr e

-- | Pretty print a command.
prettyCmd :: Cmd -> String
prettyCmd (Pen m)       = "pen " ++ prettyMode m
prettyCmd (Move l r)    = concat ["move(", prettyExpr l, ", ", prettyExpr r, ")"]
prettyCmd (Call m as)   = concat [m, "(", intercalate ", " (map prettyExpr as), ")"]
prettyCmd (For x i e b) = concat ["for ", x, " = ", prettyExpr i, " to ", prettyExpr e, " ", prettyBlock b]

-- | Pretty print a block of commands.
prettyBlock :: Block -> String
prettyBlock [] = "{}"  -- special case for empty blocks
prettyBlock cs = "{\n  " ++ indent (prettyCmds cs) ++ "\n}"
  where
    indent = concatMap (\c -> if c == '\n' then "\n  " else [c])
    prettyCmds = intercalate ";\n" . map prettyCmd

-- | Pretty print a macro definition.
prettyDef :: Def -> String
prettyDef (Define m ps b) =
    concat [m, "(", intercalate ", " ps, ") ", prettyBlock b]

-- | Pretty print a program.
pretty :: Prog -> String
pretty (Program ds b) =
    concat [intercalate "\n" (map prettyDef ds), "\nmain() ", prettyBlock b]


--
-- * Example MiniLogo programs
--

-- | A macro that draws a line between two points (x1,y1) and (x2,y2).
--
--   >>> putStrLn (prettyDef line)
--   line(x1, y1, x2, y2) {
--     pen up;
--     move(x1, y1);
--     pen down;
--     move(x2, y2)
--   }
--
line :: Def
line = Define "line" ["x1","y1","x2","y2"]
    [ Pen Up
    , Move (Ref "x1") (Ref "y1")
    , Pen Down
    , Move (Ref "x2") (Ref "y2")
    ]


-- | A macro that draws a box of width w and height h, whose bottom left corner
--   is at (x,y).
--
--   >>> putStrLn (prettyDef box)
--   box(x, y, w, h) {
--     pen up;
--     move(x, y);
--     pen down;
--     move(x + w, y);
--     move(x + w, y + h);
--     move(x, y + h);
--     move(x, y)
--   }
--
box :: Def
box = Define "box" ["x","y","w","h"]
    [ Pen Up
    , Move (Ref "x") (Ref "y")
    , Pen Down
    , Move (Add (Ref "x") (Ref "w")) (Ref "y")
    , Move (Add (Ref "x") (Ref "w")) (Add (Ref "y") (Ref "h"))
    , Move (Ref "x") (Add (Ref "y") (Ref "h"))
    , Move (Ref "x") (Ref "y")
    ]


-- | A macro that writes "HI" with the bottom left of the "H" at the
--   indicated position.
--   
--   >>> putStrLn (prettyDef hi)
--   hi(x, y) {
--     line(x, y + 2, x, y);
--     line(x + 1, y + 2, x + 1, y);
--     line(x, y + 1, x + 1, y + 1);
--     line(x + 2, y + 2, x + 2, y)
--   }
--
hi :: Def
hi = Define "hi" ["x","y"]
   [ Call "line" [ Ref "x", Add (Ref "y") (Lit 2)
                 , Ref "x", Ref "y" ]
   , Call "line" [ Add (Ref "x") (Lit 1), Add (Ref "y") (Lit 2)
                 , Add (Ref "x") (Lit 1), Ref "y" ]
   , Call "line" [ Ref "x", Add (Ref "y") (Lit 1)
                 , Add (Ref "x") (Lit 1), Add (Ref "y") (Lit 1) ]
   , Call "line" [ Add (Ref "x") (Lit 2), Add (Ref "y") (Lit 2)
                 , Add (Ref "x") (Lit 2), Ref "y" ]
   ]


-- | A macro that draws n steps starting from point (x,y).
-- 
--   >>> putStrLn (prettyDef steps)
--   steps(n, x, y) {
--     pen up;
--     move(x, y);
--     pen down;
--     for i = 0 to n + -1 {
--       move(x + i, y + i + 1);
--       move(x + i + 1, y + i + 1)
--     }
--   }
--
steps :: Def
steps = Define "steps" ["n","x","y"]
    [ Pen Up
    , Move (Ref "x") (Ref "y")
    , Pen Down
    , For "i" (Lit 0) (Add (Ref "n") (Lit (-1)))
      [ Move (Add (Ref "x") (Ref "i"))
             (Add (Add (Ref "y") (Ref "i")) (Lit 1))
      , Move (Add (Add (Ref "x") (Ref "i")) (Lit 1))
             (Add (Add (Ref "y") (Ref "i")) (Lit 1))
      ]
    ]


-- | A macro that draws an X inside a box.
-- 
--   >>> putStrLn (prettyDef xbox)
--   xbox(x, y, w, h) {
--     box(x, y, w, h);
--     line(x, y, x + w, y + h);
--     line(x, y + h, x + w, y)
--   }
--
xbox :: Def
xbox = Define "xbox" ["x","y","w","h"]
    [ Call "box" [Ref "x", Ref "y", Ref "w", Ref "h"]
    , Call "line" [Ref "x", Ref "y", Add (Ref "x") (Ref "w"), Add (Ref "y") (Ref "h")]
    , Call "line" [Ref "x", Add (Ref "y") (Ref "h"), Add (Ref "x") (Ref "w"), Ref "y"]
    ]


-- | Generate a program that draws n boxes, growing up and to the right.
--
--   >>> putStrLn (pretty (boxes 15))
--   box(x, y, w, h) {
--     pen up;
--     move(x, y);
--     pen down;
--     move(x + w, y);
--     move(x + w, y + h);
--     move(x, y + h);
--     move(x, y)
--   }
--   main() {
--     for i = 1 to 15 {
--       box(i, i, i, i)
--     }
--   }
--
boxes :: Int -> Prog
boxes n = Program [box]
    [ For "i" (Lit 1) (Lit n)
      [ Call "box" [Ref "i", Ref "i", Ref "i", Ref "i"] ]
    ]


-- | Generate a program that draws a line of n xboxes of size s, starting
--   at (1,1) and with 1 unit of space between them. (This example generously
--   sponsored by Microsoft.)
--   
--   >>> putStrLn (pretty (xboxes 5 3))
--   line(x1, y1, x2, y2) {
--     pen up;
--     move(x1, y1);
--     pen down;
--     move(x2, y2)
--   }
--   box(x, y, w, h) {
--     pen up;
--     move(x, y);
--     pen down;
--     move(x + w, y);
--     move(x + w, y + h);
--     move(x, y + h);
--     move(x, y)
--   }
--   xbox(x, y, w, h) {
--     box(x, y, w, h);
--     line(x, y, x + w, y + h);
--     line(x, y + h, x + w, y)
--   }
--   main() {
--     for i = 0 to 4 {
--       xbox(i * 4 + 1, 1, 3, 3)
--     }
--   }
--
xboxes :: Int -> Int -> Prog
xboxes n s = Program [line,box,xbox]
   [ For "i" (Lit 0) (Lit (n-1))
     [ Call "xbox" [Add (Mul (Ref "i") (Lit (s+1))) (Lit 1), Lit 1, Lit s, Lit s] ]
   ]


-- | A MiniMini logo program with a lot going on.
shebang :: Prog
shebang = Program [line,hi,box,xbox,steps]
    [ Call "hi" [Lit 39, Lit 20]
    , Call "box" [Lit 36, Lit 17, Lit 8, Lit 8]
    , Call "steps" [Lit 36, Lit 2, Lit 2]
    , Call "steps" [Lit 18, Lit 2, Lit 20]
    , Call "steps" [Lit 36, Lit 40, Lit 2]
    , Call "steps" [Lit 18, Lit 60, Lit 2]
    , Call "xbox" [Lit 25, Lit 8, Lit 3, Lit 3]
    , Call "xbox" [Lit 52, Lit 31, Lit 3, Lit 3]
    ]
