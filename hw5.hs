-- Group members:
--  * Name, ID
--  * Name, ID
--  * Name, ID
--
-- Grading notes: 15pts total
--  * 2pts checkExpr
--  * 4pts checkCmd
--  * 1pt checkBlock
--  * 1pt checkDef
--  * 2pts expr
--  * 5pts cmd
--  * + extra credit (typically 1-5pts)
--
-- Supporting files:
--
--  * MiniLogo.hs -- Defines the syntax of MiniLogo, pretty printing functions,
--    and the environment types that you'll need to implement the semantics.
--    Also includes functions to generate example MiniLogo programs to test with.
--
--  * Render.hs -- Defines the Point and Line types used in the semantics, plus
--    code for rendering the semantics of MiniLogo programs in HTML5.
--
module HW5 where

import MiniLogo
import Render
import GHC.Unicode


-- Note: in this file, we're placing the AST argument as the *last* argument in
-- each function, rather than the first argument. Although this makes the
-- semantic domains less obvious, it's good FP style since it promotes partial
-- application and can make some of your definitions a bit simpler.


-- Some functions from the Prelude that may be helpful on this assignment:
--
--   all :: (a -> Bool) -> [a] -> Bool
--     Returns true if the function returns true for every element in the list.
--
--   elem :: Eq a => a -> [a] -> Bool
--     Returns true if the first argument is contained as an element in the list.


-- This comment is defining some MiniLogo expressions used in doctests.
--
-- $setup
-- >>> let exprXY = Mul (Ref "y") (Add (Lit 3) (Ref "x"))
-- >>> let exprXZ = Add (Mul (Ref "x") (Lit 4)) (Ref "z")


--
-- * Static checker
--


-- | Statically check that a MiniLogo program is well formed. This function
--   builds up the map 'ms' that contains the defined macros and their arity
--   (i.e. the number of arguments they require), then checks all of the macro
--   definitions, and finally checks the main macro.
--
--   >>> check (xboxes 5 3)
--   True
--
--   >>> check (Program [line,xbox] [])
--   False
--
check :: Prog -> Bool
check (Program defs main) =
    all (checkDef arities) defs && checkBlock arities [] main
  where 
    entry (Define m ps _) = (m, length ps)
    arities = map entry defs



-- | Statically check that an expression is well formed by checking that there
--   are no unbound variables. This function receives as an argument a list of
--   all of the variables that are declared in the scope of the expression.
--
--   >>> checkExpr ["x"] (Ref "x")
--   True
--
--   >>> checkExpr ["y"] (Ref "x")
--   False
--
--   >>> checkExpr ["x","y"] exprXY
--   True
--
--   >>> checkExpr ["x","y"] exprXZ
--   False
--
checkExpr :: [Var] -> Expr -> Bool
checkExpr _ (Lit _) = True
checkExpr v (Ref r) = elem r v
checkExpr v (Add l r) = checkExpr v l && checkExpr v r
checkExpr v (Mul l r) = checkExpr v l && checkExpr v r

-- checkExpr (x:[]) (Lit _) = False
-- checkExpr (x:[]) (Ref r) = x == r
-- checkExpr (x:[]) (Add l r) = checkExpr [x] l || checkExpr [x] r
-- checkExpr (x:[]) (Mul l r) = checkExpr [x] l || checkExpr [x] r
-- checkExpr (x:xs) e = checkExpr [x] e && checkExpr xs e
-- checkExpr [] _ = True



-- | Statically check that a command is well formed by: (1) checking whether
--   all expressions it contains are well formed, (2) checking whether every
--   macro that is called has been defined, and (3) checking whether every
--   macro is called with the correct number of arguments. The first argument
--   to this function is a map containing the declared macros as keys and the
--   number of arguments they expect (their "arity") as values.
--
--   >>> checkCmd [] ["x","y"] (Move exprXY exprXZ)
--   False
--
--   >>> checkCmd [] ["x","y","z"] (Move exprXY exprXZ)
--   True
--
--   >>> checkCmd [] [] (Call "foo" [Lit 2, Lit 3])
--   False
--
--   >>> checkCmd [("f",2)] [] (Call "f" [Lit 2, Lit 3])
--   True
--
--   >>> checkCmd [("f",2)] [] (Call "f" [Lit 2, Lit 3, Lit 4])
--   False
--
--   >>> checkCmd [("f",2)] ["x","y","z"] (Call "f" [exprXZ, exprXY])
--   True
--
--   >>> checkCmd [("f",2)] ["x","y"] (Call "f" [exprXZ, exprXY])
--   False
--
--   >>> checkCmd [] [] (For "z" (Lit 1) (Lit 100) [Move (Ref "z") (Ref "z")])
--   True
--
--   >>> checkCmd [] [] (For "z" (Lit 1) (Lit 100) [Pen Up, Call "f" [Ref "z"]])
--   False
--
--   >>> checkCmd [("f",1)] [] (For "z" (Lit 1) (Lit 100) [Pen Up, Call "f" [Ref "z"]])
--   True
--
--   >>> checkCmd [("f",1)] [] (For "z" (Lit 1) (Lit 100) [Pen Up, Call "f" [exprXZ]])
--   False
--
--   >>> checkCmd [("f",1)] ["x"] (For "z" (Lit 1) (Lit 100) [Pen Up, Call "f" [exprXZ]])
--   True
--
--   >>> checkCmd [("f",1)] ["x"] (For "z" (Lit 1) (Lit 100) [Pen Up, Call "f" [exprXY]])
--   False
--
--   >>> checkCmd [("f",1)] ["x"] (For "z" exprXY (Lit 100) [Pen Up, Call "f" [exprXZ]])
--   False
--
--   >>> checkCmd [("f",1)] ["x"] (For "z" (Lit 1) exprXY [Pen Up, Call "f" [exprXZ]])
--   False
--
--   >>> checkCmd [("f",1)] ["x","y"] (For "z" exprXY exprXY [Pen Up, Call "f" [exprXZ]])
--   True
--
checkCmd :: Map Macro Int -> [Var] -> Cmd -> Bool
checkCmd _ v (Move l r) = checkExpr v l && checkExpr v r
checkCmd _ _ (Pen m)  = True
checkCmd m v (For fv el er b) = checkExpr (fv:v) el && checkExpr (fv:v) er && checkBlock m (fv:v) b
checkCmd m v (Call mc a)  = elem (mc,length a) m && all (checkExpr v) a



-- | Statically check whether all of the commands in a block are well formed.
--
--   >>> checkBlock [] [] []
--   True
--
--   >>> checkBlock [] ["x","y"] [Pen Up, Move exprXY exprXZ, Pen Down]
--   False
--
--   >>> checkBlock [] ["x","y","z"] [Pen Up, Move exprXY exprXZ, Pen Down]
--   True

--   >>> checkBlock [] ["x","y"] [Pen Up, Call "f" [exprXY], Pen Down]
--   False
--
--   >>> checkBlock [("f",2)] ["x","y"] [Pen Up, Call "f" [exprXY], Pen Down]
--   False
--
--   >>> checkBlock [("f",2)] ["x","y"] [Pen Up, Call "f" [exprXY,exprXZ], Pen Down]
--   False
--
--   >>> checkBlock [("f",2)] ["x","y","z"] [Pen Up, Call "f" [exprXY,exprXZ], Pen Down]
--   True
--
checkBlock :: Map Macro Int -> [Var] -> Block -> Bool
checkBlock m v (x:xs) = checkCmd m v x && checkBlock m v xs
checkBlock m v [] = True


-- | Check whether a macro definition is well formed.
--
--   >>> checkDef [] (Define "f" [] [Pen Down, Move (Lit 2) (Lit 3), Pen Up])
--   True
--
--   >>> checkDef [] (Define "f" [] [Pen Down, Move exprXY exprXZ, Pen Up])
--   False
--
--   >>> checkDef [] (Define "f" ["x","y","z"] [Pen Down, Move exprXY exprXZ, Pen Up])
--   True
--
--   >>> checkDef [] (Define "f" ["x","y","z"] [Pen Down, Call "g" [exprXY,exprXZ], Pen Up])
--   False
--
--   >>> checkDef [("g",3)] (Define "f" ["x","y","z"] [Pen Down, Call "g" [exprXY,exprXZ], Pen Up])
--   False
--
--   >>> checkDef [("g",3)] (Define "f" ["x","y","z"] [Pen Down, Call "g" [exprXY,exprXZ,exprXY], Pen Up])
--   True
--
checkDef :: Map Macro Int -> Def -> Bool
checkDef m (Define mc p b) = checkBlock m p b



--
-- * Semantics of MiniLogo
--

-- | The state of the pen, which includes whether it is up or down and its
--   current location.
type State = (Mode, Point)

-- | The initial state of the pen.
initPen :: State
initPen = (Up, (0,0))


-- | Run a MiniLogo program by:
--    1. Statically checking for errors. If it fails the check, stop here.
--    2. Run the semantics to produce a bunch of lines.
--    3. Pass those lines to the renderer.
--
--   Once your checker and semantic function are working, you should be
--   able to apply 'draw' to a MiniLogo program, then load the file
--   MiniLogo.html in your browswer to view the rendered image.
draw :: Prog -> IO ()
draw p | check p   = toHTML (prog p)
       | otherwise = putStrLn "failed static check :-("


-- ** Semantic functions

-- In this section, we're assuming we already ran the static checker. This
-- means that you can use the 'getOrFail' function to lookup entries in either
-- the variable environment or macro environment, and you can use the 'setAll'
-- function to add arguments to an environment without first checking that you
-- have the correct number.
--
-- Remember that in this assignment we're making the AST type the last argument
-- in each function to support a nicer functional programming style, even
-- though this obfuscates the semantic domains a bit. The semantic domain of
-- each syntactic category is listed below for reference and then briefly
-- explained.
--
-- Semantic domains:
--   * Expr:  Env -> Int
--   * Cmd:   Macros -> Env -> State -> (State, [Line])
--   * Block: Macros -> Env -> State -> (State, [Line])
--   * Prog:  [Line]
--
-- The semantics of expressions requires only the variable environment, and
-- this environment is read-only since expressions cannot change the values of
-- variables.

-- In addition to the variable environment, the semantics of commands and
-- blocks also takes a macro environment (Macros), which stores macro
-- definitions. The macro environment maps macro names to a pair
-- '(Pars,Block)', where the first element of the pair is the list of
-- parameters that the macro declares, and second element is the body of the
-- macro. You will have to use the macro environment in the semantics of
-- commands to implement macro calls.
--
-- Unlike in Homework 4, commands may now produce an arbitrary number of lines
-- (not just 0 or 1) because of macro calls and for loops. So, the semantic
-- domain of commands now produces a list of lines rather than a 'Maybe Line'.
--
-- Programs are run on initially empty environments and a well-defined initial
-- pen state (Up,(0,0)), so the semantic function doesn't take any arguments
-- besides the program itself. We also return only the lines drawn by the
-- program as a result since we no longer care about the pen state once the
-- program has completely finished running.



-- | Semantics of expressions.
--
--   >>> let env = [("x",3),("y",4)]
--
--   >>> expr env (Mul (Ref "y") (Add (Lit 5) (Ref "x")))
--   32
--
--   >>> expr env (Add (Mul (Ref "x") (Lit 5)) (Mul (Lit 6) (Ref "y")))
--   39
--
expr :: Env -> Expr -> Int
expr env (Ref v) = case lookup v env of
                      Just x -> x
                      Nothing -> undefined
expr _ (Lit i) = i
expr env (Add l r) = expr env l + expr env r
expr env (Mul l r) = expr env l * expr env r



-- | Semantics of commands.
--
--   >>> let vs = [("x",3),("y",4)]
--   >>> let Define _ ps b = line
--   >>> let ms = [("m1",([],[])),("line",(ps,b)),("m2",([],[]))]
--   
--   >>> cmd [] [] (Up,(2,3)) (Pen Down)
--   ((Down,(2,3)),[])
--
--   >>> cmd [] [] (Down,(2,3)) (Pen Up)
--   ((Up,(2,3)),[])
--
--   >>> cmd [] vs (Up,(2,3)) (Move (Ref "y") (Add (Ref "x") (Lit 2)))
--   ((Up,(4,5)),[])
--
--   >>> cmd [] vs (Down,(2,3)) (Move (Ref "y") (Add (Ref "x") (Lit 2)))
--   ((Down,(4,5)),[((2,3),(4,5))])
--
--   >>> cmd ms vs (Up,(0,0)) (Call "m1" [])
--   ((Up,(0,0)),[])
--
--   >>> cmd ms vs (Down,(0,0)) (Call "line" [Ref "x", Ref "y", Add (Ref "x") (Lit 2), Add (Ref "y") (Lit 3)])
--   ((Down,(5,7)),[((3,4),(5,7))])
--
--   >>> cmd [] vs (Down,(0,0)) (For "i" (Lit 1) (Ref "x") [])
--   ((Down,(0,0)),[])
--
--   >>> cmd ms vs (Down,(0,0)) (For "i" (Lit 1) (Ref "y") [Move (Ref "i") (Ref "i")])
--   ((Down,(4,4)),[((0,0),(1,1)),((1,1),(2,2)),((2,2),(3,3)),((3,3),(4,4))])
--
--   >>> cmd ms vs (Down,(0,0)) (For "i" (Ref "x") (Lit 1) [Call "line" [Ref "i", Ref "i", Mul (Ref "x") (Ref "i"), Mul (Ref "y") (Ref "i")]])
--   ((Down,(3,4)),[((3,3),(9,12)),((2,2),(6,8)),((1,1),(3,4))])
--
cmd :: Macros -> Env -> State -> Cmd -> (State, [Line])
cmd defs env state@(pen,pos) c = case c of

    Pen Up   -> ((Up,pos),[])
    Pen Down -> ((Down,pos),[])

    Move xExp yExp -> case pen of
                        Up -> ((pen,(expr env xExp,expr env yExp)),[])
                        Down -> ((pen,(expr env xExp,expr env yExp)),[(pos,(expr env xExp,expr env yExp))])

    Call macro args -> case lookup macro defs of
                        Just (pars,b) -> block defs (env++(zip pars (map (expr env) args))) state b
                        Nothing -> undefined

    For v fromExp toExp body ->

      let from = expr env fromExp
          to   = expr env toExp
          ixs  = if from <= to then [from .. to] else reverse [to .. from]

          -- This helper function runs the body of the loop once, with the loop
          -- index set to the given integer. You just need to study the code
          -- and fill in the undefined part that runs the body of the loop.
          loopStep :: (State, [Line]) -> Int -> (State, [Line])
          loopStep (s, ls) i =
            let (s', ls') = (block defs ((v,i):env) s body)
            in (s', ls ++ ls')

      in foldl loopStep (state, []) ixs



-- | Semantics of blocks.
--
--   >>> block [] [] (Down,(0,0)) []
--   ((Down,(0,0)),[])
--
--   >>> block [] [] (Down,(0,0)) [Pen Down, Pen Up, Pen Up, Move (Lit 2) (Lit 3)]
--   ((Up,(2,3)),[])
--
--   >>> block [] [] (Down,(0,0)) [Pen Up, Move (Lit 2) (Lit 3), Pen Down, Move (Lit 4) (Lit 5), Move (Lit 6) (Lit 7)]
--   ((Down,(6,7)),[((2,3),(4,5)),((4,5),(6,7))])
-- 
block :: Macros -> Env -> State -> Block -> (State, [Line])
block defs env state = go state []
  where
    go s ls []     = (s,ls)
    go s ls (c:cs) = let (s',ls') = cmd defs env s c
                     in go s' (ls ++ ls') cs



-- | Semantic function for programs.
prog :: Prog -> [Line]
prog (Program defs main) = snd $ block (map entry defs) [] initPen main
  where
    entry (Define m ps b) = (m, (ps,b))


--
-- * Amazing picture (extra credit)
--
letters=[(Define "Letter " [] []),(Define "LetterA" ["x","y"] [(Pen Up),(Move (Add (Lit 30 ) (Ref "x")) (Add (Lit 668 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 641 ) (Ref "y"))),(Move (Add (Lit 16 ) (Ref "x")) (Add (Lit 668 ) (Ref "y"))),(Move (Add (Lit 19 ) (Ref "x")) (Add (Lit 676 ) (Ref "y"))),(Move (Add (Lit 21 ) (Ref "x")) (Add (Lit 681 ) (Ref "y"))),(Move (Add (Lit 58 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 72 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 72 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 112 ) (Ref "x")) (Add (Lit 673 ) (Ref "y"))),(Move (Add (Lit 114 ) (Ref "x")) (Add (Lit 668 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 109 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 109 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 99 ) (Ref "x")) (Add (Lit 668 ) (Ref "y"))),(Move (Add (Lit 30 ) (Ref "x")) (Add (Lit 668 ) (Ref "y"))),(Pen Up),(Move (Add (Lit 65 ) (Ref "x")) (Add (Lit 761 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 35 ) (Ref "x")) (Add (Lit 681 ) (Ref "y"))),(Move (Add (Lit 94 ) (Ref "x")) (Add (Lit 681 ) (Ref "y"))),(Move (Add (Lit 65 ) (Ref "x")) (Add (Lit 761 ) (Ref "y"))),(Pen Up)]),(Define "LetterB" ["x","y"] [(Pen Up),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 679 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 119 ) (Ref "x")) (Add (Lit 659 ) (Ref "y"))),(Move (Add (Lit 105 ) (Ref "x")) (Add (Lit 646 ) (Ref "y"))),(Move (Add (Lit 86 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 86 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 95 ) (Ref "x")) (Add (Lit 779 ) (Ref "y"))),(Move (Add (Lit 105 ) (Ref "x")) (Add (Lit 775 ) (Ref "y"))),(Move (Add (Lit 113 ) (Ref "x")) (Add (Lit 769 ) (Ref "y"))),(Move (Add (Lit 119 ) (Ref "x")) (Add (Lit 761 ) (Ref "y"))),(Move (Add (Lit 123 ) (Ref "x")) (Add (Lit 752 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 742 ) (Ref "y"))),(Move (Add (Lit 122 ) (Ref "x")) (Add (Lit 730 ) (Ref "y"))),(Move (Add (Lit 116 ) (Ref "x")) (Add (Lit 719 ) (Ref "y"))),(Move (Add (Lit 107 ) (Ref "x")) (Add (Lit 710 ) (Ref "y"))),(Move (Add (Lit 116 ) (Ref "x")) (Add (Lit 702 ) (Ref "y"))),(Move (Add (Lit 122 ) (Ref "x")) (Add (Lit 691 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 679 ) (Ref "y"))),(Pen Up),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 717 ) (Ref "y"))),(Move (Add (Lit 86 ) (Ref "x")) (Add (Lit 717 ) (Ref "y"))),(Move (Add (Lit 98 ) (Ref "x")) (Add (Lit 721 ) (Ref "y"))),(Move (Add (Lit 107 ) (Ref "x")) (Add (Lit 730 ) (Ref "y"))),(Move (Add (Lit 110 ) (Ref "x")) (Add (Lit 742 ) (Ref "y"))),(Move (Add (Lit 107 ) (Ref "x")) (Add (Lit 755 ) (Ref "y"))),(Move (Add (Lit 98 ) (Ref "x")) (Add (Lit 764 ) (Ref "y"))),(Move (Add (Lit 86 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Pen Up),(Move (Add (Lit 86 ) (Ref "x")) (Add (Lit 654 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 98 ) (Ref "x")) (Add (Lit 657 ) (Ref "y"))),(Move (Add (Lit 107 ) (Ref "x")) (Add (Lit 666 ) (Ref "y"))),(Move (Add (Lit 110 ) (Ref "x")) (Add (Lit 679 ) (Ref "y"))),(Move (Add (Lit 107 ) (Ref "x")) (Add (Lit 691 ) (Ref "y"))),(Move (Add (Lit 98 ) (Ref "x")) (Add (Lit 700 ) (Ref "y"))),(Move (Add (Lit 86 ) (Ref "x")) (Add (Lit 704 ) (Ref "y"))),(Move (Add (Lit 86 ) (Ref "x")) (Add (Lit 704 ) (Ref "y"))),(Move (Add (Lit 86 ) (Ref "x")) (Add (Lit 704 ) (Ref "y"))),(Move (Add (Lit 86 ) (Ref "x")) (Add (Lit 704 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 704 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 654 ) (Ref "y"))),(Move (Add (Lit 86 ) (Ref "x")) (Add (Lit 654 ) (Ref "y"))),(Pen Up)]),(Define "LetterC" ["x","y"] [(Pen Up),(Move (Add (Lit 125 ) (Ref "x")) (Add (Lit 661 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 118 ) (Ref "x")) (Add (Lit 655 ) (Ref "y"))),(Move (Add (Lit 111 ) (Ref "x")) (Add (Lit 650 ) (Ref "y"))),(Move (Add (Lit 102 ) (Ref "x")) (Add (Lit 646 ) (Ref "y"))),(Move (Add (Lit 94 ) (Ref "x")) (Add (Lit 643 ) (Ref "y"))),(Move (Add (Lit 85 ) (Ref "x")) (Add (Lit 641 ) (Ref "y"))),(Move (Add (Lit 76 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 76 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 67 ) (Ref "x")) (Add (Lit 641 ) (Ref "y"))),(Move (Add (Lit 58 ) (Ref "x")) (Add (Lit 643 ) (Ref "y"))),(Move (Add (Lit 50 ) (Ref "x")) (Add (Lit 646 ) (Ref "y"))),(Move (Add (Lit 41 ) (Ref "x")) (Add (Lit 650 ) (Ref "y"))),(Move (Add (Lit 33 ) (Ref "x")) (Add (Lit 655 ) (Ref "y"))),(Move (Add (Lit 26 ) (Ref "x")) (Add (Lit 661 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 668 ) (Ref "y"))),(Move (Add (Lit 15 ) (Ref "x")) (Add (Lit 676 ) (Ref "y"))),(Move (Add (Lit 11 ) (Ref "x")) (Add (Lit 684 ) (Ref "y"))),(Move (Add (Lit 8 ) (Ref "x")) (Add (Lit 693 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 701 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 710 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 719 ) (Ref "y"))),(Move (Add (Lit 8 ) (Ref "x")) (Add (Lit 728 ) (Ref "y"))),(Move (Add (Lit 11 ) (Ref "x")) (Add (Lit 737 ) (Ref "y"))),(Move (Add (Lit 15 ) (Ref "x")) (Add (Lit 745 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 753 ) (Ref "y"))),(Move (Add (Lit 26 ) (Ref "x")) (Add (Lit 760 ) (Ref "y"))),(Move (Add (Lit 33 ) (Ref "x")) (Add (Lit 766 ) (Ref "y"))),(Move (Add (Lit 41 ) (Ref "x")) (Add (Lit 771 ) (Ref "y"))),(Move (Add (Lit 50 ) (Ref "x")) (Add (Lit 775 ) (Ref "y"))),(Move (Add (Lit 58 ) (Ref "x")) (Add (Lit 778 ) (Ref "y"))),(Move (Add (Lit 67 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 76 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 85 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 94 ) (Ref "x")) (Add (Lit 778 ) (Ref "y"))),(Move (Add (Lit 102 ) (Ref "x")) (Add (Lit 775 ) (Ref "y"))),(Move (Add (Lit 111 ) (Ref "x")) (Add (Lit 771 ) (Ref "y"))),(Move (Add (Lit 118 ) (Ref "x")) (Add (Lit 766 ) (Ref "y"))),(Move (Add (Lit 125 ) (Ref "x")) (Add (Lit 760 ) (Ref "y"))),(Move (Add (Lit 125 ) (Ref "x")) (Add (Lit 760 ) (Ref "y"))),(Move (Add (Lit 125 ) (Ref "x")) (Add (Lit 760 ) (Ref "y"))),(Move (Add (Lit 116 ) (Ref "x")) (Add (Lit 750 ) (Ref "y"))),(Move (Add (Lit 116 ) (Ref "x")) (Add (Lit 750 ) (Ref "y"))),(Move (Add (Lit 110 ) (Ref "x")) (Add (Lit 755 ) (Ref "y"))),(Move (Add (Lit 104 ) (Ref "x")) (Add (Lit 759 ) (Ref "y"))),(Move (Add (Lit 98 ) (Ref "x")) (Add (Lit 763 ) (Ref "y"))),(Move (Add (Lit 91 ) (Ref "x")) (Add (Lit 765 ) (Ref "y"))),(Move (Add (Lit 83 ) (Ref "x")) (Add (Lit 766 ) (Ref "y"))),(Move (Add (Lit 76 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Move (Add (Lit 61 ) (Ref "x")) (Add (Lit 765 ) (Ref "y"))),(Move (Add (Lit 48 ) (Ref "x")) (Add (Lit 759 ) (Ref "y"))),(Move (Add (Lit 36 ) (Ref "x")) (Add (Lit 750 ) (Ref "y"))),(Move (Add (Lit 27 ) (Ref "x")) (Add (Lit 739 ) (Ref "y"))),(Move (Add (Lit 21 ) (Ref "x")) (Add (Lit 725 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 710 ) (Ref "y"))),(Move (Add (Lit 21 ) (Ref "x")) (Add (Lit 696 ) (Ref "y"))),(Move (Add (Lit 27 ) (Ref "x")) (Add (Lit 682 ) (Ref "y"))),(Move (Add (Lit 36 ) (Ref "x")) (Add (Lit 671 ) (Ref "y"))),(Move (Add (Lit 48 ) (Ref "x")) (Add (Lit 662 ) (Ref "y"))),(Move (Add (Lit 61 ) (Ref "x")) (Add (Lit 656 ) (Ref "y"))),(Move (Add (Lit 76 ) (Ref "x")) (Add (Lit 654 ) (Ref "y"))),(Move (Add (Lit 91 ) (Ref "x")) (Add (Lit 656 ) (Ref "y"))),(Move (Add (Lit 104 ) (Ref "x")) (Add (Lit 662 ) (Ref "y"))),(Move (Add (Lit 116 ) (Ref "x")) (Add (Lit 671 ) (Ref "y"))),(Move (Add (Lit 116 ) (Ref "x")) (Add (Lit 671 ) (Ref "y"))),(Move (Add (Lit 116 ) (Ref "x")) (Add (Lit 671 ) (Ref "y"))),(Move (Add (Lit 125 ) (Ref "x")) (Add (Lit 661 ) (Ref "y"))),(Move (Add (Lit 125 ) (Ref "x")) (Add (Lit 661 ) (Ref "y"))),(Pen Up)]),(Define "LetterD" ["x","y"] [(Pen Up),(Move (Add (Lit 103 ) (Ref "x")) (Add (Lit 661 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 97 ) (Ref "x")) (Add (Lit 655 ) (Ref "y"))),(Move (Add (Lit 89 ) (Ref "x")) (Add (Lit 650 ) (Ref "y"))),(Move (Add (Lit 81 ) (Ref "x")) (Add (Lit 646 ) (Ref "y"))),(Move (Add (Lit 72 ) (Ref "x")) (Add (Lit 643 ) (Ref "y"))),(Move (Add (Lit 63 ) (Ref "x")) (Add (Lit 641 ) (Ref "y"))),(Move (Add (Lit 54 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 19 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 54 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 63 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 72 ) (Ref "x")) (Add (Lit 778 ) (Ref "y"))),(Move (Add (Lit 81 ) (Ref "x")) (Add (Lit 775 ) (Ref "y"))),(Move (Add (Lit 89 ) (Ref "x")) (Add (Lit 771 ) (Ref "y"))),(Move (Add (Lit 97 ) (Ref "x")) (Add (Lit 766 ) (Ref "y"))),(Move (Add (Lit 103 ) (Ref "x")) (Add (Lit 760 ) (Ref "y"))),(Move (Add (Lit 109 ) (Ref "x")) (Add (Lit 753 ) (Ref "y"))),(Move (Add (Lit 114 ) (Ref "x")) (Add (Lit 746 ) (Ref "y"))),(Move (Add (Lit 118 ) (Ref "x")) (Add (Lit 738 ) (Ref "y"))),(Move (Add (Lit 121 ) (Ref "x")) (Add (Lit 729 ) (Ref "y"))),(Move (Add (Lit 123 ) (Ref "x")) (Add (Lit 720 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 710 ) (Ref "y"))),(Move (Add (Lit 123 ) (Ref "x")) (Add (Lit 701 ) (Ref "y"))),(Move (Add (Lit 121 ) (Ref "x")) (Add (Lit 692 ) (Ref "y"))),(Move (Add (Lit 118 ) (Ref "x")) (Add (Lit 683 ) (Ref "y"))),(Move (Add (Lit 114 ) (Ref "x")) (Add (Lit 675 ) (Ref "y"))),(Move (Add (Lit 109 ) (Ref "x")) (Add (Lit 668 ) (Ref "y"))),(Move (Add (Lit 103 ) (Ref "x")) (Add (Lit 661 ) (Ref "y"))),(Pen Up),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 654 ) (Ref "y"))),(Move (Add (Lit 54 ) (Ref "x")) (Add (Lit 654 ) (Ref "y"))),(Move (Add (Lit 82 ) (Ref "x")) (Add (Lit 662 ) (Ref "y"))),(Move (Add (Lit 103 ) (Ref "x")) (Add (Lit 682 ) (Ref "y"))),(Move (Add (Lit 110 ) (Ref "x")) (Add (Lit 710 ) (Ref "y"))),(Move (Add (Lit 103 ) (Ref "x")) (Add (Lit 739 ) (Ref "y"))),(Move (Add (Lit 82 ) (Ref "x")) (Add (Lit 759 ) (Ref "y"))),(Move (Add (Lit 54 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Pen Up)]),(Define "LetterE" ["x","y"] [(Pen Up),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 717 ) (Ref "y"))),(Move (Add (Lit 93 ) (Ref "x")) (Add (Lit 717 ) (Ref "y"))),(Move (Add (Lit 93 ) (Ref "x")) (Add (Lit 704 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 704 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 654 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 654 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Pen Up)]),(Define "LetterF" ["x","y"] [(Pen Up),(Move (Add (Lit 93 ) (Ref "x")) (Add (Lit 717 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 93 ) (Ref "x")) (Add (Lit 704 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 704 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 19 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 717 ) (Ref "y"))),(Move (Add (Lit 93 ) (Ref "x")) (Add (Lit 717 ) (Ref "y"))),(Pen Up)]),(Define "LetterG" ["x","y"] [(Pen Up),(Move (Add (Lit 116 ) (Ref "x")) (Add (Lit 750 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 90 ) (Ref "x")) (Add (Lit 765 ) (Ref "y"))),(Move (Add (Lit 62 ) (Ref "x")) (Add (Lit 765 ) (Ref "y"))),(Move (Add (Lit 36 ) (Ref "x")) (Add (Lit 750 ) (Ref "y"))),(Move (Add (Lit 21 ) (Ref "x")) (Add (Lit 725 ) (Ref "y"))),(Move (Add (Lit 21 ) (Ref "x")) (Add (Lit 696 ) (Ref "y"))),(Move (Add (Lit 36 ) (Ref "x")) (Add (Lit 671 ) (Ref "y"))),(Move (Add (Lit 43 ) (Ref "x")) (Add (Lit 665 ) (Ref "y"))),(Move (Add (Lit 50 ) (Ref "x")) (Add (Lit 660 ) (Ref "y"))),(Move (Add (Lit 58 ) (Ref "x")) (Add (Lit 657 ) (Ref "y"))),(Move (Add (Lit 58 ) (Ref "x")) (Add (Lit 657 ) (Ref "y"))),(Move (Add (Lit 58 ) (Ref "x")) (Add (Lit 657 ) (Ref "y"))),(Move (Add (Lit 58 ) (Ref "x")) (Add (Lit 657 ) (Ref "y"))),(Move (Add (Lit 58 ) (Ref "x")) (Add (Lit 657 ) (Ref "y"))),(Move (Add (Lit 59 ) (Ref "x")) (Add (Lit 657 ) (Ref "y"))),(Move (Add (Lit 59 ) (Ref "x")) (Add (Lit 657 ) (Ref "y"))),(Move (Add (Lit 70 ) (Ref "x")) (Add (Lit 654 ) (Ref "y"))),(Move (Add (Lit 82 ) (Ref "x")) (Add (Lit 654 ) (Ref "y"))),(Move (Add (Lit 93 ) (Ref "x")) (Add (Lit 657 ) (Ref "y"))),(Move (Add (Lit 100 ) (Ref "x")) (Add (Lit 659 ) (Ref "y"))),(Move (Add (Lit 106 ) (Ref "x")) (Add (Lit 663 ) (Ref "y"))),(Move (Add (Lit 112 ) (Ref "x")) (Add (Lit 667 ) (Ref "y"))),(Move (Add (Lit 112 ) (Ref "x")) (Add (Lit 717 ) (Ref "y"))),(Move (Add (Lit 125 ) (Ref "x")) (Add (Lit 717 ) (Ref "y"))),(Move (Add (Lit 125 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 125 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 112 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 112 ) (Ref "x")) (Add (Lit 650 ) (Ref "y"))),(Move (Add (Lit 105 ) (Ref "x")) (Add (Lit 647 ) (Ref "y"))),(Move (Add (Lit 98 ) (Ref "x")) (Add (Lit 644 ) (Ref "y"))),(Move (Add (Lit 91 ) (Ref "x")) (Add (Lit 642 ) (Ref "y"))),(Move (Add (Lit 83 ) (Ref "x")) (Add (Lit 641 ) (Ref "y"))),(Move (Add (Lit 75 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 68 ) (Ref "x")) (Add (Lit 641 ) (Ref "y"))),(Move (Add (Lit 60 ) (Ref "x")) (Add (Lit 642 ) (Ref "y"))),(Move (Add (Lit 53 ) (Ref "x")) (Add (Lit 644 ) (Ref "y"))),(Move (Add (Lit 46 ) (Ref "x")) (Add (Lit 647 ) (Ref "y"))),(Move (Add (Lit 39 ) (Ref "x")) (Add (Lit 651 ) (Ref "y"))),(Move (Add (Lit 32 ) (Ref "x")) (Add (Lit 656 ) (Ref "y"))),(Move (Add (Lit 26 ) (Ref "x")) (Add (Lit 661 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 668 ) (Ref "y"))),(Move (Add (Lit 15 ) (Ref "x")) (Add (Lit 676 ) (Ref "y"))),(Move (Add (Lit 11 ) (Ref "x")) (Add (Lit 684 ) (Ref "y"))),(Move (Add (Lit 8 ) (Ref "x")) (Add (Lit 693 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 701 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 710 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 719 ) (Ref "y"))),(Move (Add (Lit 8 ) (Ref "x")) (Add (Lit 728 ) (Ref "y"))),(Move (Add (Lit 11 ) (Ref "x")) (Add (Lit 737 ) (Ref "y"))),(Move (Add (Lit 15 ) (Ref "x")) (Add (Lit 745 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 753 ) (Ref "y"))),(Move (Add (Lit 26 ) (Ref "x")) (Add (Lit 760 ) (Ref "y"))),(Move (Add (Lit 33 ) (Ref "x")) (Add (Lit 766 ) (Ref "y"))),(Move (Add (Lit 41 ) (Ref "x")) (Add (Lit 771 ) (Ref "y"))),(Move (Add (Lit 50 ) (Ref "x")) (Add (Lit 775 ) (Ref "y"))),(Move (Add (Lit 58 ) (Ref "x")) (Add (Lit 778 ) (Ref "y"))),(Move (Add (Lit 67 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 76 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 85 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 94 ) (Ref "x")) (Add (Lit 778 ) (Ref "y"))),(Move (Add (Lit 102 ) (Ref "x")) (Add (Lit 775 ) (Ref "y"))),(Move (Add (Lit 111 ) (Ref "x")) (Add (Lit 771 ) (Ref "y"))),(Move (Add (Lit 118 ) (Ref "x")) (Add (Lit 766 ) (Ref "y"))),(Move (Add (Lit 125 ) (Ref "x")) (Add (Lit 760 ) (Ref "y"))),(Move (Add (Lit 125 ) (Ref "x")) (Add (Lit 760 ) (Ref "y"))),(Move (Add (Lit 125 ) (Ref "x")) (Add (Lit 760 ) (Ref "y"))),(Move (Add (Lit 122 ) (Ref "x")) (Add (Lit 756 ) (Ref "y"))),(Move (Add (Lit 116 ) (Ref "x")) (Add (Lit 750 ) (Ref "y"))),(Move (Add (Lit 116 ) (Ref "x")) (Add (Lit 750 ) (Ref "y"))),(Pen Up),(Move (Add (Lit 90 ) (Ref "x")) (Add (Lit 650 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 80 ) (Ref "x")) (Add (Lit 649 ) (Ref "y"))),(Move (Add (Lit 71 ) (Ref "x")) (Add (Lit 649 ) (Ref "y"))),(Move (Add (Lit 61 ) (Ref "x")) (Add (Lit 650 ) (Ref "y"))),(Move (Add (Lit 71 ) (Ref "x")) (Add (Lit 649 ) (Ref "y"))),(Move (Add (Lit 80 ) (Ref "x")) (Add (Lit 649 ) (Ref "y"))),(Move (Add (Lit 90 ) (Ref "x")) (Add (Lit 650 ) (Ref "y"))),(Pen Up)]),(Define "LetterH" ["x","y"] [(Pen Up),(Move (Add (Lit 110 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 110 ) (Ref "x")) (Add (Lit 704 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 704 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 717 ) (Ref "y"))),(Move (Add (Lit 110 ) (Ref "x")) (Add (Lit 717 ) (Ref "y"))),(Move (Add (Lit 110 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 110 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Pen Up)]),(Define "LetterI" ["x","y"] [(Pen Up),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Pen Up)]),(Define "LetterJ" ["x","y"] [(Pen Up),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 699 ) (Ref "y"))),(Move (Add (Lit 123 ) (Ref "x")) (Add (Lit 692 ) (Ref "y"))),(Move (Add (Lit 122 ) (Ref "x")) (Add (Lit 684 ) (Ref "y"))),(Move (Add (Lit 119 ) (Ref "x")) (Add (Lit 676 ) (Ref "y"))),(Move (Add (Lit 116 ) (Ref "x")) (Add (Lit 670 ) (Ref "y"))),(Move (Add (Lit 112 ) (Ref "x")) (Add (Lit 663 ) (Ref "y"))),(Move (Add (Lit 107 ) (Ref "x")) (Add (Lit 658 ) (Ref "y"))),(Move (Add (Lit 101 ) (Ref "x")) (Add (Lit 653 ) (Ref "y"))),(Move (Add (Lit 95 ) (Ref "x")) (Add (Lit 648 ) (Ref "y"))),(Move (Add (Lit 88 ) (Ref "x")) (Add (Lit 645 ) (Ref "y"))),(Move (Add (Lit 80 ) (Ref "x")) (Add (Lit 643 ) (Ref "y"))),(Move (Add (Lit 73 ) (Ref "x")) (Add (Lit 641 ) (Ref "y"))),(Move (Add (Lit 65 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 57 ) (Ref "x")) (Add (Lit 641 ) (Ref "y"))),(Move (Add (Lit 49 ) (Ref "x")) (Add (Lit 643 ) (Ref "y"))),(Move (Add (Lit 42 ) (Ref "x")) (Add (Lit 645 ) (Ref "y"))),(Move (Add (Lit 35 ) (Ref "x")) (Add (Lit 648 ) (Ref "y"))),(Move (Add (Lit 29 ) (Ref "x")) (Add (Lit 653 ) (Ref "y"))),(Move (Add (Lit 23 ) (Ref "x")) (Add (Lit 658 ) (Ref "y"))),(Move (Add (Lit 18 ) (Ref "x")) (Add (Lit 663 ) (Ref "y"))),(Move (Add (Lit 14 ) (Ref "x")) (Add (Lit 670 ) (Ref "y"))),(Move (Add (Lit 11 ) (Ref "x")) (Add (Lit 676 ) (Ref "y"))),(Move (Add (Lit 8 ) (Ref "x")) (Add (Lit 684 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 692 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 699 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 700 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 700 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 699 ) (Ref "y"))),(Move (Add (Lit 26 ) (Ref "x")) (Add (Lit 677 ) (Ref "y"))),(Move (Add (Lit 42 ) (Ref "x")) (Add (Lit 660 ) (Ref "y"))),(Move (Add (Lit 65 ) (Ref "x")) (Add (Lit 654 ) (Ref "y"))),(Move (Add (Lit 88 ) (Ref "x")) (Add (Lit 660 ) (Ref "y"))),(Move (Add (Lit 104 ) (Ref "x")) (Add (Lit 677 ) (Ref "y"))),(Move (Add (Lit 110 ) (Ref "x")) (Add (Lit 699 ) (Ref "y"))),(Move (Add (Lit 110 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Pen Up)]),(Define "LetterK" ["x","y"] [(Pen Up),(Move (Add (Lit 21 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 21 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 659 ) (Ref "y"))),(Move (Add (Lit 65 ) (Ref "x")) (Add (Lit 722 ) (Ref "y"))),(Move (Add (Lit 107 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 73 ) (Ref "x")) (Add (Lit 710 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 119 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 119 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 109 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 109 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 107 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 107 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 65 ) (Ref "x")) (Add (Lit 699 ) (Ref "y"))),(Move (Add (Lit 23 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 21 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Pen Up)]),(Define "LetterL" ["x","y"] [(Pen Up),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 654 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 654 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Pen Up)]),(Define "LetterM" ["x","y"] [(Pen Up),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 23 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 23 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 75 ) (Ref "x")) (Add (Lit 708 ) (Ref "y"))),(Move (Add (Lit 128 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 145 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 145 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 145 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 145 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 131 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 131 ) (Ref "x")) (Add (Lit 762 ) (Ref "y"))),(Move (Add (Lit 75 ) (Ref "x")) (Add (Lit 684 ) (Ref "y"))),(Move (Add (Lit 75 ) (Ref "x")) (Add (Lit 684 ) (Ref "y"))),(Move (Add (Lit 72 ) (Ref "x")) (Add (Lit 689 ) (Ref "y"))),(Move (Add (Lit 70 ) (Ref "x")) (Add (Lit 691 ) (Ref "y"))),(Move (Add (Lit 60 ) (Ref "x")) (Add (Lit 706 ) (Ref "y"))),(Move (Add (Lit 57 ) (Ref "x")) (Add (Lit 710 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 762 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Pen Up)]),(Define "LetterN" ["x","y"] [(Pen Up),(Move (Add (Lit 110 ) (Ref "x")) (Add (Lit 659 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 110 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 110 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 110 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 107 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 107 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 57 ) (Ref "x")) (Add (Lit 710 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 762 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 23 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 23 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 110 ) (Ref "x")) (Add (Lit 659 ) (Ref "y"))),(Pen Up)]),(Define "LetterO" ["x","y"] [(Pen Up),(Move (Add (Lit 125 ) (Ref "x")) (Add (Lit 760 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 131 ) (Ref "x")) (Add (Lit 753 ) (Ref "y"))),(Move (Add (Lit 136 ) (Ref "x")) (Add (Lit 746 ) (Ref "y"))),(Move (Add (Lit 140 ) (Ref "x")) (Add (Lit 738 ) (Ref "y"))),(Move (Add (Lit 144 ) (Ref "x")) (Add (Lit 729 ) (Ref "y"))),(Move (Add (Lit 145 ) (Ref "x")) (Add (Lit 720 ) (Ref "y"))),(Move (Add (Lit 146 ) (Ref "x")) (Add (Lit 710 ) (Ref "y"))),(Move (Add (Lit 145 ) (Ref "x")) (Add (Lit 701 ) (Ref "y"))),(Move (Add (Lit 144 ) (Ref "x")) (Add (Lit 692 ) (Ref "y"))),(Move (Add (Lit 140 ) (Ref "x")) (Add (Lit 683 ) (Ref "y"))),(Move (Add (Lit 136 ) (Ref "x")) (Add (Lit 675 ) (Ref "y"))),(Move (Add (Lit 131 ) (Ref "x")) (Add (Lit 668 ) (Ref "y"))),(Move (Add (Lit 125 ) (Ref "x")) (Add (Lit 661 ) (Ref "y"))),(Move (Add (Lit 119 ) (Ref "x")) (Add (Lit 655 ) (Ref "y"))),(Move (Add (Lit 111 ) (Ref "x")) (Add (Lit 650 ) (Ref "y"))),(Move (Add (Lit 103 ) (Ref "x")) (Add (Lit 646 ) (Ref "y"))),(Move (Add (Lit 94 ) (Ref "x")) (Add (Lit 643 ) (Ref "y"))),(Move (Add (Lit 85 ) (Ref "x")) (Add (Lit 641 ) (Ref "y"))),(Move (Add (Lit 76 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 67 ) (Ref "x")) (Add (Lit 641 ) (Ref "y"))),(Move (Add (Lit 57 ) (Ref "x")) (Add (Lit 643 ) (Ref "y"))),(Move (Add (Lit 49 ) (Ref "x")) (Add (Lit 646 ) (Ref "y"))),(Move (Add (Lit 41 ) (Ref "x")) (Add (Lit 650 ) (Ref "y"))),(Move (Add (Lit 33 ) (Ref "x")) (Add (Lit 655 ) (Ref "y"))),(Move (Add (Lit 26 ) (Ref "x")) (Add (Lit 661 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 668 ) (Ref "y"))),(Move (Add (Lit 15 ) (Ref "x")) (Add (Lit 675 ) (Ref "y"))),(Move (Add (Lit 11 ) (Ref "x")) (Add (Lit 683 ) (Ref "y"))),(Move (Add (Lit 8 ) (Ref "x")) (Add (Lit 692 ) (Ref "y"))),(Move (Add (Lit 7 ) (Ref "x")) (Add (Lit 701 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 710 ) (Ref "y"))),(Move (Add (Lit 7 ) (Ref "x")) (Add (Lit 720 ) (Ref "y"))),(Move (Add (Lit 8 ) (Ref "x")) (Add (Lit 729 ) (Ref "y"))),(Move (Add (Lit 11 ) (Ref "x")) (Add (Lit 738 ) (Ref "y"))),(Move (Add (Lit 15 ) (Ref "x")) (Add (Lit 746 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 753 ) (Ref "y"))),(Move (Add (Lit 26 ) (Ref "x")) (Add (Lit 760 ) (Ref "y"))),(Move (Add (Lit 33 ) (Ref "x")) (Add (Lit 766 ) (Ref "y"))),(Move (Add (Lit 41 ) (Ref "x")) (Add (Lit 771 ) (Ref "y"))),(Move (Add (Lit 49 ) (Ref "x")) (Add (Lit 775 ) (Ref "y"))),(Move (Add (Lit 57 ) (Ref "x")) (Add (Lit 778 ) (Ref "y"))),(Move (Add (Lit 67 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 76 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 85 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 94 ) (Ref "x")) (Add (Lit 778 ) (Ref "y"))),(Move (Add (Lit 103 ) (Ref "x")) (Add (Lit 775 ) (Ref "y"))),(Move (Add (Lit 111 ) (Ref "x")) (Add (Lit 771 ) (Ref "y"))),(Move (Add (Lit 119 ) (Ref "x")) (Add (Lit 766 ) (Ref "y"))),(Move (Add (Lit 125 ) (Ref "x")) (Add (Lit 760 ) (Ref "y"))),(Pen Up),(Move (Add (Lit 76 ) (Ref "x")) (Add (Lit 654 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 104 ) (Ref "x")) (Add (Lit 662 ) (Ref "y"))),(Move (Add (Lit 125 ) (Ref "x")) (Add (Lit 682 ) (Ref "y"))),(Move (Add (Lit 132 ) (Ref "x")) (Add (Lit 710 ) (Ref "y"))),(Move (Add (Lit 125 ) (Ref "x")) (Add (Lit 739 ) (Ref "y"))),(Move (Add (Lit 104 ) (Ref "x")) (Add (Lit 759 ) (Ref "y"))),(Move (Add (Lit 76 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Move (Add (Lit 48 ) (Ref "x")) (Add (Lit 759 ) (Ref "y"))),(Move (Add (Lit 27 ) (Ref "x")) (Add (Lit 739 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 710 ) (Ref "y"))),(Move (Add (Lit 27 ) (Ref "x")) (Add (Lit 682 ) (Ref "y"))),(Move (Add (Lit 48 ) (Ref "x")) (Add (Lit 662 ) (Ref "y"))),(Move (Add (Lit 76 ) (Ref "x")) (Add (Lit 654 ) (Ref "y"))),(Pen Up)]),(Define "LetterP" ["x","y"] [(Pen Up),(Move (Add (Lit 74 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 87 ) (Ref "x")) (Add (Lit 779 ) (Ref "y"))),(Move (Add (Lit 99 ) (Ref "x")) (Add (Lit 774 ) (Ref "y"))),(Move (Add (Lit 109 ) (Ref "x")) (Add (Lit 766 ) (Ref "y"))),(Move (Add (Lit 117 ) (Ref "x")) (Add (Lit 755 ) (Ref "y"))),(Move (Add (Lit 122 ) (Ref "x")) (Add (Lit 743 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 730 ) (Ref "y"))),(Move (Add (Lit 122 ) (Ref "x")) (Add (Lit 717 ) (Ref "y"))),(Move (Add (Lit 117 ) (Ref "x")) (Add (Lit 705 ) (Ref "y"))),(Move (Add (Lit 109 ) (Ref "x")) (Add (Lit 695 ) (Ref "y"))),(Move (Add (Lit 99 ) (Ref "x")) (Add (Lit 687 ) (Ref "y"))),(Move (Add (Lit 87 ) (Ref "x")) (Add (Lit 682 ) (Ref "y"))),(Move (Add (Lit 74 ) (Ref "x")) (Add (Lit 680 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 680 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 74 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Pen Up),(Move (Add (Lit 74 ) (Ref "x")) (Add (Lit 694 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 92 ) (Ref "x")) (Add (Lit 699 ) (Ref "y"))),(Move (Add (Lit 105 ) (Ref "x")) (Add (Lit 712 ) (Ref "y"))),(Move (Add (Lit 110 ) (Ref "x")) (Add (Lit 730 ) (Ref "y"))),(Move (Add (Lit 105 ) (Ref "x")) (Add (Lit 749 ) (Ref "y"))),(Move (Add (Lit 92 ) (Ref "x")) (Add (Lit 762 ) (Ref "y"))),(Move (Add (Lit 74 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 694 ) (Ref "y"))),(Move (Add (Lit 74 ) (Ref "x")) (Add (Lit 694 ) (Ref "y"))),(Pen Up)]),(Define "LetterQ" ["x","y"] [(Pen Up),(Move (Add (Lit 146 ) (Ref "x")) (Add (Lit 710 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 144 ) (Ref "x")) (Add (Lit 694 ) (Ref "y"))),(Move (Add (Lit 138 ) (Ref "x")) (Add (Lit 678 ) (Ref "y"))),(Move (Add (Lit 129 ) (Ref "x")) (Add (Lit 664 ) (Ref "y"))),(Move (Add (Lit 146 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 129 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 129 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 119 ) (Ref "x")) (Add (Lit 655 ) (Ref "y"))),(Move (Add (Lit 112 ) (Ref "x")) (Add (Lit 651 ) (Ref "y"))),(Move (Add (Lit 106 ) (Ref "x")) (Add (Lit 647 ) (Ref "y"))),(Move (Add (Lit 99 ) (Ref "x")) (Add (Lit 644 ) (Ref "y"))),(Move (Add (Lit 91 ) (Ref "x")) (Add (Lit 642 ) (Ref "y"))),(Move (Add (Lit 84 ) (Ref "x")) (Add (Lit 641 ) (Ref "y"))),(Move (Add (Lit 76 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 67 ) (Ref "x")) (Add (Lit 641 ) (Ref "y"))),(Move (Add (Lit 57 ) (Ref "x")) (Add (Lit 643 ) (Ref "y"))),(Move (Add (Lit 49 ) (Ref "x")) (Add (Lit 646 ) (Ref "y"))),(Move (Add (Lit 41 ) (Ref "x")) (Add (Lit 650 ) (Ref "y"))),(Move (Add (Lit 33 ) (Ref "x")) (Add (Lit 655 ) (Ref "y"))),(Move (Add (Lit 26 ) (Ref "x")) (Add (Lit 661 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 668 ) (Ref "y"))),(Move (Add (Lit 15 ) (Ref "x")) (Add (Lit 675 ) (Ref "y"))),(Move (Add (Lit 11 ) (Ref "x")) (Add (Lit 683 ) (Ref "y"))),(Move (Add (Lit 8 ) (Ref "x")) (Add (Lit 692 ) (Ref "y"))),(Move (Add (Lit 7 ) (Ref "x")) (Add (Lit 701 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 710 ) (Ref "y"))),(Move (Add (Lit 7 ) (Ref "x")) (Add (Lit 720 ) (Ref "y"))),(Move (Add (Lit 8 ) (Ref "x")) (Add (Lit 729 ) (Ref "y"))),(Move (Add (Lit 11 ) (Ref "x")) (Add (Lit 738 ) (Ref "y"))),(Move (Add (Lit 15 ) (Ref "x")) (Add (Lit 746 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 753 ) (Ref "y"))),(Move (Add (Lit 26 ) (Ref "x")) (Add (Lit 760 ) (Ref "y"))),(Move (Add (Lit 33 ) (Ref "x")) (Add (Lit 766 ) (Ref "y"))),(Move (Add (Lit 41 ) (Ref "x")) (Add (Lit 771 ) (Ref "y"))),(Move (Add (Lit 49 ) (Ref "x")) (Add (Lit 775 ) (Ref "y"))),(Move (Add (Lit 57 ) (Ref "x")) (Add (Lit 778 ) (Ref "y"))),(Move (Add (Lit 67 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 76 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 85 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 94 ) (Ref "x")) (Add (Lit 778 ) (Ref "y"))),(Move (Add (Lit 103 ) (Ref "x")) (Add (Lit 775 ) (Ref "y"))),(Move (Add (Lit 111 ) (Ref "x")) (Add (Lit 771 ) (Ref "y"))),(Move (Add (Lit 119 ) (Ref "x")) (Add (Lit 766 ) (Ref "y"))),(Move (Add (Lit 125 ) (Ref "x")) (Add (Lit 760 ) (Ref "y"))),(Move (Add (Lit 131 ) (Ref "x")) (Add (Lit 753 ) (Ref "y"))),(Move (Add (Lit 136 ) (Ref "x")) (Add (Lit 746 ) (Ref "y"))),(Move (Add (Lit 140 ) (Ref "x")) (Add (Lit 738 ) (Ref "y"))),(Move (Add (Lit 144 ) (Ref "x")) (Add (Lit 729 ) (Ref "y"))),(Move (Add (Lit 145 ) (Ref "x")) (Add (Lit 720 ) (Ref "y"))),(Move (Add (Lit 146 ) (Ref "x")) (Add (Lit 710 ) (Ref "y"))),(Pen Up),(Move (Add (Lit 90 ) (Ref "x")) (Add (Lit 717 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 120 ) (Ref "x")) (Add (Lit 676 ) (Ref "y"))),(Move (Add (Lit 127 ) (Ref "x")) (Add (Lit 686 ) (Ref "y"))),(Move (Add (Lit 131 ) (Ref "x")) (Add (Lit 698 ) (Ref "y"))),(Move (Add (Lit 132 ) (Ref "x")) (Add (Lit 710 ) (Ref "y"))),(Move (Add (Lit 125 ) (Ref "x")) (Add (Lit 739 ) (Ref "y"))),(Move (Add (Lit 104 ) (Ref "x")) (Add (Lit 759 ) (Ref "y"))),(Move (Add (Lit 76 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Move (Add (Lit 48 ) (Ref "x")) (Add (Lit 759 ) (Ref "y"))),(Move (Add (Lit 27 ) (Ref "x")) (Add (Lit 739 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 710 ) (Ref "y"))),(Move (Add (Lit 27 ) (Ref "x")) (Add (Lit 682 ) (Ref "y"))),(Move (Add (Lit 48 ) (Ref "x")) (Add (Lit 662 ) (Ref "y"))),(Move (Add (Lit 76 ) (Ref "x")) (Add (Lit 654 ) (Ref "y"))),(Move (Add (Lit 88 ) (Ref "x")) (Add (Lit 655 ) (Ref "y"))),(Move (Add (Lit 100 ) (Ref "x")) (Add (Lit 659 ) (Ref "y"))),(Move (Add (Lit 111 ) (Ref "x")) (Add (Lit 666 ) (Ref "y"))),(Move (Add (Lit 74 ) (Ref "x")) (Add (Lit 717 ) (Ref "y"))),(Move (Add (Lit 90 ) (Ref "x")) (Add (Lit 717 ) (Ref "y"))),(Move (Add (Lit 90 ) (Ref "x")) (Add (Lit 717 ) (Ref "y"))),(Pen Up)]),(Define "LetterR" ["x","y"] [(Pen Up),(Move (Add (Lit 115 ) (Ref "x")) (Add (Lit 702 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 109 ) (Ref "x")) (Add (Lit 694 ) (Ref "y"))),(Move (Add (Lit 101 ) (Ref "x")) (Add (Lit 688 ) (Ref "y"))),(Move (Add (Lit 93 ) (Ref "x")) (Add (Lit 684 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 107 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 107 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 78 ) (Ref "x")) (Add (Lit 680 ) (Ref "y"))),(Move (Add (Lit 77 ) (Ref "x")) (Add (Lit 680 ) (Ref "y"))),(Move (Add (Lit 75 ) (Ref "x")) (Add (Lit 680 ) (Ref "y"))),(Move (Add (Lit 74 ) (Ref "x")) (Add (Lit 680 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 680 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 19 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 74 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 87 ) (Ref "x")) (Add (Lit 779 ) (Ref "y"))),(Move (Add (Lit 99 ) (Ref "x")) (Add (Lit 774 ) (Ref "y"))),(Move (Add (Lit 109 ) (Ref "x")) (Add (Lit 766 ) (Ref "y"))),(Move (Add (Lit 117 ) (Ref "x")) (Add (Lit 755 ) (Ref "y"))),(Move (Add (Lit 122 ) (Ref "x")) (Add (Lit 743 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 730 ) (Ref "y"))),(Move (Add (Lit 123 ) (Ref "x")) (Add (Lit 720 ) (Ref "y"))),(Move (Add (Lit 120 ) (Ref "x")) (Add (Lit 711 ) (Ref "y"))),(Move (Add (Lit 115 ) (Ref "x")) (Add (Lit 702 ) (Ref "y"))),(Pen Up),(Move (Add (Lit 79 ) (Ref "x")) (Add (Lit 694 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 80 ) (Ref "x")) (Add (Lit 694 ) (Ref "y"))),(Move (Add (Lit 82 ) (Ref "x")) (Add (Lit 695 ) (Ref "y"))),(Move (Add (Lit 84 ) (Ref "x")) (Add (Lit 695 ) (Ref "y"))),(Move (Add (Lit 98 ) (Ref "x")) (Add (Lit 703 ) (Ref "y"))),(Move (Add (Lit 107 ) (Ref "x")) (Add (Lit 715 ) (Ref "y"))),(Move (Add (Lit 110 ) (Ref "x")) (Add (Lit 730 ) (Ref "y"))),(Move (Add (Lit 105 ) (Ref "x")) (Add (Lit 749 ) (Ref "y"))),(Move (Add (Lit 92 ) (Ref "x")) (Add (Lit 762 ) (Ref "y"))),(Move (Add (Lit 74 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 694 ) (Ref "y"))),(Move (Add (Lit 74 ) (Ref "x")) (Add (Lit 694 ) (Ref "y"))),(Move (Add (Lit 74 ) (Ref "x")) (Add (Lit 694 ) (Ref "y"))),(Move (Add (Lit 75 ) (Ref "x")) (Add (Lit 694 ) (Ref "y"))),(Move (Add (Lit 75 ) (Ref "x")) (Add (Lit 694 ) (Ref "y"))),(Move (Add (Lit 76 ) (Ref "x")) (Add (Lit 694 ) (Ref "y"))),(Move (Add (Lit 77 ) (Ref "x")) (Add (Lit 694 ) (Ref "y"))),(Move (Add (Lit 79 ) (Ref "x")) (Add (Lit 694 ) (Ref "y"))),(Pen Up)]),(Define "LetterS" ["x","y"] [(Pen Up),(Move (Add (Lit 86 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 95 ) (Ref "x")) (Add (Lit 779 ) (Ref "y"))),(Move (Add (Lit 105 ) (Ref "x")) (Add (Lit 775 ) (Ref "y"))),(Move (Add (Lit 113 ) (Ref "x")) (Add (Lit 769 ) (Ref "y"))),(Move (Add (Lit 119 ) (Ref "x")) (Add (Lit 761 ) (Ref "y"))),(Move (Add (Lit 123 ) (Ref "x")) (Add (Lit 752 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 742 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 742 ) (Ref "y"))),(Move (Add (Lit 110 ) (Ref "x")) (Add (Lit 742 ) (Ref "y"))),(Move (Add (Lit 110 ) (Ref "x")) (Add (Lit 742 ) (Ref "y"))),(Move (Add (Lit 107 ) (Ref "x")) (Add (Lit 755 ) (Ref "y"))),(Move (Add (Lit 98 ) (Ref "x")) (Add (Lit 764 ) (Ref "y"))),(Move (Add (Lit 85 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Move (Add (Lit 44 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Move (Add (Lit 32 ) (Ref "x")) (Add (Lit 763 ) (Ref "y"))),(Move (Add (Lit 23 ) (Ref "x")) (Add (Lit 755 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 742 ) (Ref "y"))),(Move (Add (Lit 23 ) (Ref "x")) (Add (Lit 730 ) (Ref "y"))),(Move (Add (Lit 32 ) (Ref "x")) (Add (Lit 721 ) (Ref "y"))),(Move (Add (Lit 44 ) (Ref "x")) (Add (Lit 717 ) (Ref "y"))),(Move (Add (Lit 86 ) (Ref "x")) (Add (Lit 717 ) (Ref "y"))),(Move (Add (Lit 95 ) (Ref "x")) (Add (Lit 716 ) (Ref "y"))),(Move (Add (Lit 105 ) (Ref "x")) (Add (Lit 712 ) (Ref "y"))),(Move (Add (Lit 113 ) (Ref "x")) (Add (Lit 706 ) (Ref "y"))),(Move (Add (Lit 119 ) (Ref "x")) (Add (Lit 698 ) (Ref "y"))),(Move (Add (Lit 123 ) (Ref "x")) (Add (Lit 689 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 679 ) (Ref "y"))),(Move (Add (Lit 123 ) (Ref "x")) (Add (Lit 669 ) (Ref "y"))),(Move (Add (Lit 119 ) (Ref "x")) (Add (Lit 660 ) (Ref "y"))),(Move (Add (Lit 113 ) (Ref "x")) (Add (Lit 652 ) (Ref "y"))),(Move (Add (Lit 105 ) (Ref "x")) (Add (Lit 646 ) (Ref "y"))),(Move (Add (Lit 95 ) (Ref "x")) (Add (Lit 642 ) (Ref "y"))),(Move (Add (Lit 86 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 44 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 34 ) (Ref "x")) (Add (Lit 642 ) (Ref "y"))),(Move (Add (Lit 25 ) (Ref "x")) (Add (Lit 646 ) (Ref "y"))),(Move (Add (Lit 17 ) (Ref "x")) (Add (Lit 652 ) (Ref "y"))),(Move (Add (Lit 11 ) (Ref "x")) (Add (Lit 660 ) (Ref "y"))),(Move (Add (Lit 7 ) (Ref "x")) (Add (Lit 669 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 679 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 679 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 679 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 679 ) (Ref "y"))),(Move (Add (Lit 23 ) (Ref "x")) (Add (Lit 666 ) (Ref "y"))),(Move (Add (Lit 32 ) (Ref "x")) (Add (Lit 657 ) (Ref "y"))),(Move (Add (Lit 44 ) (Ref "x")) (Add (Lit 654 ) (Ref "y"))),(Move (Add (Lit 85 ) (Ref "x")) (Add (Lit 654 ) (Ref "y"))),(Move (Add (Lit 98 ) (Ref "x")) (Add (Lit 657 ) (Ref "y"))),(Move (Add (Lit 107 ) (Ref "x")) (Add (Lit 666 ) (Ref "y"))),(Move (Add (Lit 110 ) (Ref "x")) (Add (Lit 679 ) (Ref "y"))),(Move (Add (Lit 107 ) (Ref "x")) (Add (Lit 691 ) (Ref "y"))),(Move (Add (Lit 98 ) (Ref "x")) (Add (Lit 700 ) (Ref "y"))),(Move (Add (Lit 85 ) (Ref "x")) (Add (Lit 704 ) (Ref "y"))),(Move (Add (Lit 44 ) (Ref "x")) (Add (Lit 704 ) (Ref "y"))),(Move (Add (Lit 34 ) (Ref "x")) (Add (Lit 705 ) (Ref "y"))),(Move (Add (Lit 25 ) (Ref "x")) (Add (Lit 709 ) (Ref "y"))),(Move (Add (Lit 17 ) (Ref "x")) (Add (Lit 715 ) (Ref "y"))),(Move (Add (Lit 11 ) (Ref "x")) (Add (Lit 723 ) (Ref "y"))),(Move (Add (Lit 7 ) (Ref "x")) (Add (Lit 732 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 742 ) (Ref "y"))),(Move (Add (Lit 11 ) (Ref "x")) (Add (Lit 761 ) (Ref "y"))),(Move (Add (Lit 25 ) (Ref "x")) (Add (Lit 775 ) (Ref "y"))),(Move (Add (Lit 44 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 86 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Pen Up)]),(Define "LetterT" ["x","y"] [(Pen Up),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Move (Add (Lit 72 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Move (Add (Lit 72 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 58 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 58 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Pen Up)]),(Define "LetterU" ["x","y"] [(Pen Up),(Move (Add (Lit 110 ) (Ref "x")) (Add (Lit 699 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 110 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 699 ) (Ref "y"))),(Move (Add (Lit 123 ) (Ref "x")) (Add (Lit 692 ) (Ref "y"))),(Move (Add (Lit 122 ) (Ref "x")) (Add (Lit 684 ) (Ref "y"))),(Move (Add (Lit 119 ) (Ref "x")) (Add (Lit 676 ) (Ref "y"))),(Move (Add (Lit 116 ) (Ref "x")) (Add (Lit 670 ) (Ref "y"))),(Move (Add (Lit 112 ) (Ref "x")) (Add (Lit 663 ) (Ref "y"))),(Move (Add (Lit 107 ) (Ref "x")) (Add (Lit 658 ) (Ref "y"))),(Move (Add (Lit 101 ) (Ref "x")) (Add (Lit 653 ) (Ref "y"))),(Move (Add (Lit 95 ) (Ref "x")) (Add (Lit 648 ) (Ref "y"))),(Move (Add (Lit 88 ) (Ref "x")) (Add (Lit 645 ) (Ref "y"))),(Move (Add (Lit 80 ) (Ref "x")) (Add (Lit 643 ) (Ref "y"))),(Move (Add (Lit 73 ) (Ref "x")) (Add (Lit 641 ) (Ref "y"))),(Move (Add (Lit 65 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 57 ) (Ref "x")) (Add (Lit 641 ) (Ref "y"))),(Move (Add (Lit 49 ) (Ref "x")) (Add (Lit 643 ) (Ref "y"))),(Move (Add (Lit 42 ) (Ref "x")) (Add (Lit 645 ) (Ref "y"))),(Move (Add (Lit 35 ) (Ref "x")) (Add (Lit 648 ) (Ref "y"))),(Move (Add (Lit 29 ) (Ref "x")) (Add (Lit 653 ) (Ref "y"))),(Move (Add (Lit 23 ) (Ref "x")) (Add (Lit 658 ) (Ref "y"))),(Move (Add (Lit 18 ) (Ref "x")) (Add (Lit 663 ) (Ref "y"))),(Move (Add (Lit 14 ) (Ref "x")) (Add (Lit 670 ) (Ref "y"))),(Move (Add (Lit 11 ) (Ref "x")) (Add (Lit 676 ) (Ref "y"))),(Move (Add (Lit 8 ) (Ref "x")) (Add (Lit 684 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 692 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 699 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 699 ) (Ref "y"))),(Move (Add (Lit 26 ) (Ref "x")) (Add (Lit 677 ) (Ref "y"))),(Move (Add (Lit 42 ) (Ref "x")) (Add (Lit 660 ) (Ref "y"))),(Move (Add (Lit 65 ) (Ref "x")) (Add (Lit 654 ) (Ref "y"))),(Move (Add (Lit 88 ) (Ref "x")) (Add (Lit 660 ) (Ref "y"))),(Move (Add (Lit 104 ) (Ref "x")) (Add (Lit 677 ) (Ref "y"))),(Move (Add (Lit 110 ) (Ref "x")) (Add (Lit 699 ) (Ref "y"))),(Pen Up)]),(Define "LetterV" ["x","y"] [(Pen Up),(Move (Add (Lit 65 ) (Ref "x")) (Add (Lit 660 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 109 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 114 ) (Ref "x")) (Add (Lit 753 ) (Ref "y"))),(Move (Add (Lit 112 ) (Ref "x")) (Add (Lit 748 ) (Ref "y"))),(Move (Add (Lit 109 ) (Ref "x")) (Add (Lit 740 ) (Ref "y"))),(Move (Add (Lit 72 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 58 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 58 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 18 ) (Ref "x")) (Add (Lit 748 ) (Ref "y"))),(Move (Add (Lit 16 ) (Ref "x")) (Add (Lit 753 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 65 ) (Ref "x")) (Add (Lit 660 ) (Ref "y"))),(Pen Up)]),(Define "LetterW" ["x","y"] [(Pen Up),(Move (Add (Lit 116 ) (Ref "x")) (Add (Lit 660 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 160 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 175 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 175 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 165 ) (Ref "x")) (Add (Lit 753 ) (Ref "y"))),(Move (Add (Lit 163 ) (Ref "x")) (Add (Lit 748 ) (Ref "y"))),(Move (Add (Lit 160 ) (Ref "x")) (Add (Lit 740 ) (Ref "y"))),(Move (Add (Lit 123 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 108 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 108 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 90 ) (Ref "x")) (Add (Lit 690 ) (Ref "y"))),(Move (Add (Lit 72 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 58 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 58 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 18 ) (Ref "x")) (Add (Lit 748 ) (Ref "y"))),(Move (Add (Lit 16 ) (Ref "x")) (Add (Lit 753 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 20 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 65 ) (Ref "x")) (Add (Lit 660 ) (Ref "y"))),(Move (Add (Lit 83 ) (Ref "x")) (Add (Lit 709 ) (Ref "y"))),(Move (Add (Lit 69 ) (Ref "x")) (Add (Lit 748 ) (Ref "y"))),(Move (Add (Lit 67 ) (Ref "x")) (Add (Lit 753 ) (Ref "y"))),(Move (Add (Lit 57 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 71 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 71 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 90 ) (Ref "x")) (Add (Lit 729 ) (Ref "y"))),(Move (Add (Lit 109 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 114 ) (Ref "x")) (Add (Lit 753 ) (Ref "y"))),(Move (Add (Lit 111 ) (Ref "x")) (Add (Lit 745 ) (Ref "y"))),(Move (Add (Lit 109 ) (Ref "x")) (Add (Lit 740 ) (Ref "y"))),(Move (Add (Lit 98 ) (Ref "x")) (Add (Lit 709 ) (Ref "y"))),(Move (Add (Lit 116 ) (Ref "x")) (Add (Lit 660 ) (Ref "y"))),(Pen Up)]),(Define "LetterX" ["x","y"] [(Pen Up),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 73 ) (Ref "x")) (Add (Lit 710 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 107 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 107 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 65 ) (Ref "x")) (Add (Lit 699 ) (Ref "y"))),(Move (Add (Lit 23 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 641 ) (Ref "y"))),(Move (Add (Lit 57 ) (Ref "x")) (Add (Lit 710 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 23 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 23 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 65 ) (Ref "x")) (Add (Lit 722 ) (Ref "y"))),(Move (Add (Lit 107 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Pen Up)]),(Define "LetterY" ["x","y"] [(Pen Up),(Move (Add (Lit 65 ) (Ref "x")) (Add (Lit 722 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 107 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 72 ) (Ref "x")) (Add (Lit 708 ) (Ref "y"))),(Move (Add (Lit 72 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 58 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 58 ) (Ref "x")) (Add (Lit 708 ) (Ref "y"))),(Move (Add (Lit 57 ) (Ref "x")) (Add (Lit 710 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 23 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 23 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 65 ) (Ref "x")) (Add (Lit 722 ) (Ref "y"))),(Pen Up)]),(Define "LetterZ" ["x","y"] [(Pen Up),(Move (Add (Lit 114 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Pen Down),(Move (Add (Lit 33 ) (Ref "x")) (Add (Lit 654 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 654 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 21 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 21 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 11 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 11 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 640 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 641 ) (Ref "y"))),(Move (Add (Lit 97 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Move (Add (Lit 6 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 124 ) (Ref "x")) (Add (Lit 780 ) (Ref "y"))),(Move (Add (Lit 114 ) (Ref "x")) (Add (Lit 767 ) (Ref "y"))),(Pen Up)])]

buildBlock :: (Int,Int) -> String -> Block
buildBlock (ix,iy) ('\n':xs) = buildBlock (0,iy-160) xs
buildBlock (ix,iy) (' ':xs) = buildBlock (ix+120,iy) xs
buildBlock (ix,iy) ('\t':xs) = buildBlock (ix+120*4,iy) xs
buildBlock (ix,iy) ('I':xs) = (Call ("Letter"++['I']) [((Lit ix)),(Lit iy)]):(buildBlock (ix+40,iy) xs)
buildBlock (ix,iy) ('W':xs) = (Call ("Letter"++['W']) [((Lit ix)),(Lit iy)]):(buildBlock (ix+175,iy) xs)
buildBlock (ix,iy) (x:xs) = (Call ("Letter"++[x]) [((Lit ix)),(Lit iy)]):(buildBlock (ix+150,iy) xs)
buildBlock _ [] = []

buildProg :: String -> Prog
buildProg s = Program letters (buildBlock (0,10000-160*5) (map toUpper s))
              where 
                newLineCount :: String -> Int
                newLineCount ('\n':xs) = 1+newLineCount xs
                newLineCount (_:xs) = newLineCount xs
                newLineCount [] = 0

-- | A MiniLogo program that draws your amazing picture.
amazing :: Prog
amazing = buildProg "Hello there\n\nProcess\n\tFirst I got the kavo font on fontspace\n\tSecond Converted each letter to a plate\n\tThird used Bash and Sed to force to ints\n\tFourth used a python script to parse the plate into a MiniLogo Block\n\tFifth appended into Haskell for your enjoyment\n\nA through Z as well as space tab and newline are added\nI hope you are having a good day\n\t\tSee Ya"