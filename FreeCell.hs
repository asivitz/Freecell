{-|
Module      : FreeCell
Description : A library for Freecell
Copyright   : (c) Timothy Dees, 2014
License     : MIT
Maintainer  : timothy.dees@gmail.com
Stability   : experimental

This lets you play FreeCell.  It's fun, I think.
-}

module FreeCell 
    (  -- * Types to work with playing cards
      Rank
    , Suit
    , Card
    , Stack
    , Cascade
    , Foundation
    , Freecell
    , Board
    , GameState
    , FCTree
    , Location
    , Move
    , Solution
    , -- * Utility functions to work with playing cards
      red
    , black
    , deck
    , -- * Functions to make, play, and solve games
      makeGame
    , playGame
    , solveRandomGame
    , treeSolverPruned
    , treeSolverDF
    , deckShuffle
    , allPermissable
    , solvedBoard
    , -- * I/O with games
      loadFile
    , loadBoardFromText
    , -- * Accessor functions for the card types 
      rank
    , suit
    , cascades
    , foundations
    , freecells
    , gameBoard
    , sourceMove
    ) 
where

import Control.Applicative ((<$>))
import Control.Monad.State.Lazy

import Data.Function (on)
import Data.List
import Data.Maybe
import Data.Tree

import System.Random

-- |Type to represent the rank of a card, from Ace to King.
data Rank = Ace | Two | Three | Four | Five | Six | Seven | Eight |
        Nine | Ten | Jack | Queen | King
        
  deriving (Show, Eq, Enum, Ord)

-- |Type to represent suit of a card.
data Suit 
    = Heart 
    | Diamond 
    | Club 
    | Spade 
    
  deriving (Show, Eq, Enum, Ord)

-- |Type to represent a playing card.  Has a suit and a rank.
data Card = Card 
    { rank :: Rank
    , suit :: Suit 
    } 
    
  deriving (Show, Eq, Ord)

-- |Type alias to represent a stack of cards.
type Stack = [Card]

newtype Cascade = Cascade [Card] deriving Eq

newtype Foundation = Foundation [Card] deriving Eq

newtype Freecell = Freecell (Maybe Card) deriving Eq

class CardStack a where
        cards :: CardStack a => a -> [Card]
        pushCard :: CardStack a => a -> Card -> a
        emptyStack :: CardStack a => a -> Bool
        emptyStack cs = null (cards cs)
        popCard :: CardStack a => a -> a
        topCard :: CardStack a => a -> Maybe Card
        topCard a = case cards a of
                        x:xs -> Just x
                        [] -> Nothing

instance CardStack Cascade where
        cards (Cascade cs) = cs
        pushCard (Cascade cs) c = Cascade (c:cs)
        popCard (Cascade (c:cs)) = Cascade cs
        popCard (Cascade []) = error "Can't pop card from empty cascade."

instance CardStack Foundation where
        cards (Foundation cs) = cs
        pushCard (Foundation cs) c = Foundation (c:cs)
        popCard (Foundation (c:cs)) = Foundation cs
        popCard (Foundation []) = error "Can't pop card from empty foundation."

instance CardStack Freecell where
        cards (Freecell Nothing) = []
        cards (Freecell (Just c)) = [c]
        pushCard (Freecell Nothing) c = error "Can't push card onto filled freecell."
        pushCard (Freecell _) c = Freecell (Just c)
        popCard (Freecell Nothing) = error "Can't pop card from empty freecell."
        popCard (Freecell _) = Freecell Nothing

-- |Type to represent a game board: 8 cascades, 4 foundations, 4 freecells.
-- Freecells are represented by a list instead of a set to preserve order 
-- for UI implementations.
data Board = Board 
    { cascades    :: [Cascade]
    , foundations :: [Foundation]
    , freecells   ::  [Freecell]
    } 
    
  {-deriving Ord-}

removeEmpty :: CardStack a => [a] -> [a]
removeEmpty = filter (not . emptyStack)

instance Eq Board where
    Board cs fd fc == Board cs' fd' fc' = 
        and [ fd == fd'
            , removeEmpty fc == removeEmpty fc'
            , removeEmpty cs == removeEmpty cs'
            ]

instance Show Board where
    show (Board cs fd fc) = 
        unlines [csstring, fdstring, fcstring]

      where
        csstring = unlines $ for cs $ ("C "  ++) . unwords . map cardString . cards
        fdstring = unlines $ for fd $ ("FD " ++) . unwords . map cardString . cards
        fcstring = "FC " ++ unwords (map cardString . (foldl (++) []) $ (map cards) fc)

for = flip map

-- |Type to hold the location of a card.
data Location 
    = Cascades Int 
    | CascadesSource 
    | Foundations 
    | FreeCells 
    
  deriving (Show, Eq)


-- |Type holds a card, it's prior location, and it's eventual location.  Alternately,
-- it can hold BeginGame, which just represents that this was the initial board.
data Move 
    = Move Card Location Location 
    | BeginGame 
    
  deriving Eq

-- |Type to hold a board and the move that resulted in that board.
data GameState = GameState 
    { gameBoard  :: Board
    , sourceMove :: Move 
    } 
    
  deriving (Show, Eq)

-- | Type alias to use for tree constructed for the solver.
type FCTree = Tree [GameState]

-- |Just a list of moves.
data Solution = Solution [Move]

instance Show Solution where
    show (Solution moves) = case moves of
        BeginGame : xs ->           show (Solution xs)
        x         : xs -> show x ++ show (Solution xs)
        _              -> ""

instance Show Move where
    show move = case move of 
        Move (Card rk st) l1 l2 ->
            show rk ++ " " ++ 
            show st ++ ": " ++ 
            show l1 ++ " -> " ++ 
            show l2 ++ "\n"
        
        BeginGame -> 
            ""

-- |Returns whether a card is red.
red :: Card -> Bool
red (Card _ st) = st `elem` [Heart, Diamond]

-- |Returns whether a card is black.
black :: Card -> Bool
black = not . red

-- |Associative list for the suits.
suitAssoc :: [(Int, Suit)]
suitAssoc = zip [0..] [Heart .. Spade]

-- |Push a card into a cascade.
pushCascade :: Board -> Card -> Int -> Board
pushCascade (Board cs fd fc) cd num = 
    Board cs' fd fc

  where 
    cs' = applyAt cs num (`pushCard` cd)

-- |Pop a card out of a cascade.
popCascade :: Board -> Card -> Board
popCascade (Board cs fd fc) cd = 
    Board cs' fd fc

  where
    cs' = stackf $ removeEmpty cs

    stackf [] = [] 
    stackf (x :xs) 
        | topCard x == Just cd = popCard x : xs
        | otherwise       = x : stackf xs

-- |Push a card into a foundation stack.
pushFoundation :: Board -> Card -> Board
pushFoundation (Board cs fd fc) (Card rk st) = 
    Board cs fd' fc

  where 
    fd' = applyAt fd num (`pushCard` (Card rk st))
    num = fromJust $ elemIndex st [Heart .. Spade]

modifyFirstWhere :: (a -> Bool) -> (a -> a) -> [a] -> [a]
modifyFirstWhere _ _ [] = []
modifyFirstWhere p f (x:xs)
    | p x = (f x) : xs
    | otherwise = x : (modifyFirstWhere p f xs)

-- |Push a card into a freecell.
pushFreeCell :: Board -> Card -> Board
pushFreeCell (Board cs fd fc) cd = 
    Board cs fd 
    $ modifyFirstWhere emptyStack (`pushCard` cd) fc

-- |Pop a card out of a freecell.
popFreeCell :: Board -> Card -> Board
popFreeCell (Board cs fd fc) card =
    Board cs fd fc'

  where 
    fc' = modifyFirstWhere (\x -> maybe False (==card) (topCard x)) popCard fc

-- |Just a dumb function to attempt to identify to score moves.  Needs work, clearly.
entropyScore :: Board -> Int
entropyScore (Board cs fd fc) = 
    nullPoints + buriedFDs + runs

  where
    nullPoints = 6 * (length (filter emptyStack fc) - length (filter emptyStack cs))

    runs = sum $ map (runlength . cards) cs

    runlength stack = case stack of
        Card King _ : _ -> -1
        
        x1 : x2 : xs ->
            if   x2 `continues` x1
            then -1 + runlength (x2:xs)
            else  0
            
        _ : _ -> -1
        [] ->     0
        
    nextCard (Foundation stack) = case stack of
        []           -> Card   Ace
        Card x _ : _ -> Card $ safesucc x
    
    nextCards = 
        for suitAssoc $ \(x,y) -> 
            nextCard (fd !! x) y

    buriedFDs = (*3) 
        $ sum 
        $ (map cards cs) `concatFor` findIndices (`elem` nextCards)

    continues x2 x1 = 
        and [ succ (rank x1) == rank  x2
            , red        x1  == black x2
            ]

-- |Determines which cascades a card can be played on.
playableCascades :: Board -> Card -> [Int]
playableCascades (Board stacks _ _) cd = 
    findIndices playableCascade stacks

  where
    playableCascade (Cascade stack) = case stack of
        []             -> True
        Card Ace _ : _ -> False
        st         : _ ->
            and [ black cd == red        st
                , rank  cd == pred (rank st)
                ]

-- |Determines if a card can be played on the foundation stacks.
playableFoundation :: Board -> Card -> Bool
playableFoundation (Board _ xs _) (Card rk st) = 
    playableFoundation' (xs !! num)

  where 
    num = fromJust $ elemIndex st [Heart .. Spade]

    playableFoundation' (Foundation stack) = case stack of
        []    -> rk == Ace
        y : _ -> rk == succ (rank y)

-- |Determines if a board has available freecells.
playableFreeCell :: Board -> Bool
playableFreeCell (Board _ _ fc) = length fc < 4

-- |Determines all legal plays for a given Board and Card.
allCardPlays :: Board -> Card -> Location -> [GameState]
allCardPlays bd card source = 
    allCardPlaysNoFC bd card source ++ fcplays

  where
    fcplays = 
        [GameState 
            (pushFreeCell bd card) 
            (Move card source FreeCells) 
        
        | playableFreeCell bd
        ]

-- |Determines all legal plays excluding freecells.  Not sure this is necessary...
allCardPlaysNoFC :: Board -> Card -> Location -> [GameState]
allCardPlaysNoFC bd card source = pf ++ stackplays

  where
    pf = [GameState 
            (pushFoundation bd card) 
            (Move card source Foundations) 
            
         | playableFoundation bd card
         ]
         
    cascadeInts   = playableCascades bd card
    cascadeBoards = for cascadeInts $ pushCascade bd card
    
    stackplays = zip cascadeBoards cascadeInts `for` \(x, y) -> 
        GameState x $ Move card source $ Cascades y

-- |Determines which cards are available to be played from the cascades.
availableCascadeCards :: Board -> [Card]
availableCascadeCards (Board cs _ _) = 
    map (head . cards) $ filter (not . emptyStack) cs

-- |Determines which cards are in the freecells.
availableFreeCellCards :: Board -> Stack
availableFreeCellCards = (foldl (++) []) . (map cards) . freecells

-- |Utility function to succ the rank of a card without throwing an error if you succ a King.
safesucc :: Rank -> Rank
safesucc card = case card of
    King -> King
    x    -> succ x

-- |Determines which card is the highest rank of card of a given color that can be forced into a move.
highestForceable :: [[Card]] -> Bool -> Rank
highestForceable stacks bool = case (stacks, bool) of
    ([[],[],_ ,_ ], False) -> Two
    ([_ ,_ ,[],[]], True)  -> Two
    ([he,di,cl,sp], rd) 
        | null stack1 || null stack2 -> Two
        | otherwise                  -> lesser

      where 
        (stack1, stack2) = if not rd then (he, di) else (cl, sp)
        
        lesser = safesucc $ rank $ head $ if rank (head stack1) > rank (head stack2) then stack2 else stack1

    _ -> Two

-- |Determines which moves to the foundations should be forced 
-- (i.e. an Ace is played automatically to the foundations.)
forcedMove :: GameState -> Bool
forcedMove (GameState (Board _ fd _) (Move cd _ Foundations)) =
        rank cd <= highestForceable (map cards fd) (red cd)

forcedMove _ = False

-- |Determines all of the permissable moves for a given board.
allPermissable :: Board -> [GameState]
allPermissable bd = 
    filter ((/= bd) . gameBoard)
        $ if null forced
          then moves
          else take 1 forced
  where
    forced = filter forcedMove moves
  
    fccards  = availableFreeCellCards bd
    fcboards = for fccards $ popFreeCell bd
    
    cscards  = availableCascadeCards bd
    csboards = for cscards $ popCascade bd
    
    crds  = fccards  ++ cscards
    boards = fcboards ++ csboards
    
    sources = 
        replicate (length fccards) FreeCells ++ 
        replicate (length cscards) CascadesSource
              
    moves =
        zip3 boards crds sources `concatFor` \(a,b,c) -> 
            allCardPlays a b c
            
concatFor = flip concatMap

-- |Checks if a board is solved.
solvedBoard :: Board -> Bool
solvedBoard (Board cs _ fc) = all emptyStack cs && all emptyStack fc

-- |Builds the lazy tree to hold all board moves.
buildTree :: Board -> FCTree
buildTree bd = 
    unfoldTree f [GameState bd BeginGame]

  where 
    f b = (b, moves)

      where    
        moves = map (:b) val
     
        val = 
            filter (not . (`elem` map gameBoard b) . gameBoard) $
            sortBy (compare `on` (entropyScore . gameBoard)) $
            allPermissable $ 
            gameBoard $ 
            head b

-- |Checks the depth-first flattened structure of the board for a solution.
-- Naive and slow.
treeSolverDF :: Board -> Solution
treeSolverDF = Solution 
    . map sourceMove 
    . reverse 
    . head 
    . filter (solvedBoard . gameBoard . head) 
    . flatten 
    . buildTree

-- |Prunes the tree of any already-check boards and uses this tree to solve
-- the puzzle.  Has an annoying habit of eating up lots of memory and dying.  Needs
-- work.
treeSolverPruned :: Board -> Solution
treeSolverPruned = Solution 
    . map sourceMove 
    . reverse 
    . head 
    . check 
    . buildTree

-- |Prunes the tree and solves the game (in theory!).
check :: FCTree -> [[GameState]]
check tr = 
    evalState (check' tr) []

  where 
    check' (Node s forests) = do
        bdlst <- get

        let bd = gameBoard $ head s

        if solvedBoard bd 
        then do
            return [s] 

        else if any (==bd) bdlst 
        then do
            return [] 
            
        else do
            modify (bd:) 

            concat `fmap` mapM check' forests

-- |Loads a game in the appropriate format.
-- Format is:
--     ranks -> A, 2, 3, 4, 5, 6, 7, 8, 9, T, J, Q, K
--     suits -> H, D, S, C
--     cards -> i.e. AH, 4D, etc.
--     cascades -> C 4H 2S ...
--     freecells -> FC 2H 3S ...
--     foundations -> FD 2H AH
-- Note that the left-most card is the bottom card on a cascade
-- and the top card on a foundation.
loadFile :: FilePath -> IO Board
loadFile x = loadBoardFromText <$> readFile x

newFoundations :: [Foundation]
newFoundations = replicate 4 (Foundation [])

newFreecells :: [Freecell]
newFreecells = replicate 4 (Freecell Nothing)

-- |Loads a board from a string.  The foundations part is implemented wrong, 
-- and I'll probably fix it or something.
loadBoardFromText :: String -> Board
loadBoardFromText rawtext = 
    case lines rawtext `loadBoard` ([], [], []) of
        (cs, fd, fc) -> Board cs fd fc

  where
    loadBoard :: [String] -> ([Cascade], [Foundation], [Freecell]) -> ([Cascade], [Foundation], [Freecell])
    loadBoard strings emp = foldl (\(cs, fd, fc) list -> case list of
        'C' : ' ' :       s -> (cs ++ [(Cascade $ parse s)], fd, fc)
        'F' : 'C' : ' ' : s -> (cs, fd, map (Freecell . Just) (parse s))
        'F' : ' ' :       s -> (cs, (Foundation $ parse s) : fd, fc)
        _                   -> (cs, fd, fc))
        emp strings

    
    parse = map parser . words

-- |Parses a two-character string into a card.
parser :: String -> Card
parser (rankChar : rest) =
    Card rk st

  where
    rk = fromMaybe (error $ "Bad parse string: " ++ (rankChar : rest))
        $ rankChar `lookup` zip "23456789TJQKA" [Two ..]
        
    st = suitParser rest
parser _ = error "Can't parse Card if not two characters."
        
-- |Returns a single character for each rank.
cardChar :: Rank -> Char
cardChar c = case c of
    Ace   -> 'A'
    King  -> 'K'
    Queen -> 'Q'
    Jack  -> 'J'
    Ten   -> 'T'
    Nine  -> '9'
    Eight -> '8'
    Seven -> '7'
    Six   -> '6'
    Five  -> '5'
    Four  -> '4'
    Three -> '3'
    Two   -> '2'

-- |Returns a character for each suit.
suitChar :: Suit -> Char
suitChar s = case s of
    Heart   -> 'H'
    Club    -> 'C'
    Diamond -> 'D'
    Spade   -> 'S'

-- |Returns a string for each card.
cardString :: Card -> String
cardString (Card rk st) = [cardChar rk, suitChar st]

-- |Parses a string into a suit
suitParser :: String -> Suit
suitParser x = case x of
    "H" -> Heart
    "C" -> Club
    "D" -> Diamond
    "S" -> Spade
    _ -> error $ "Unrecognized suit: " ++ x

-- |A list of all 52 cards.
deck :: [Card]
deck = [Card x y | x <- [Ace ..], y <- [Heart ..]]

-- |Shuffles a deck using the IO random generator.
deckShuffle :: Eq a => [a] -> IO [a]
deckShuffle [] = return []
deckShuffle xs = do
        x <- randomRIO (0, length xs-1) :: IO Int

        let val = xs !! x

        y <- deckShuffle $ xs \\ [val]

        return $ val : y

-- |Makes a game for you to play!
makeGame :: IO Board
makeGame = do
    s <- deckShuffle deck

    let (s0, l1) = splitAt 7 s
        (s1, l2) = splitAt 7 l1
        (s2, l3) = splitAt 7 l2
        (s3, l4) = splitAt 7 l3
        (s4, l5) = splitAt 6 l4
        (s5, l6) = splitAt 6 l5
        (s6, l7) = splitAt 6 l6
       
        s7 = l7
        cs = [s0,s1,s2,s3,s4,s5,s6,s7]
        
    return $ Board (map Cascade cs) newFoundations newFreecells

-- |Text based Freecell game.
playGame :: IO ()
playGame = do
    gm <- makeGame

    playloop gm
    
  where
    playloop g = do
        print g
        putStrLn ("Entropy: " ++ show (entropyScore g))

        if solvedBoard g 
        then putStrLn "You win!" 
        else do
            let
                states   = allPermissable g
                
                moves    = map sourceMove states
                boards   = map gameBoard  states
                
                movenums = [0..length moves]
                
                selMove = do
                    selectedMove <- read <$> getLine :: IO Int
                    
                    if (selectedMove >= length moves) || (selectedMove < 0) 
                    then do
                        putStrLn "Invalid move, select again."
                        selMove 
                        
                    else 
                        return selectedMove
                        
            if null moves 
            then putStrLn "No possible moves, you lose." 
            else 
                if length moves == 1 
                then do
                    putStrLn "Move forced .... " 
                    playloop (head boards) 
                    
                else do
                    putStrLn "Select next move from list: "
                    putStrLn $ zip movenums moves `concatFor` \(x,y) -> 
                        show x ++ ": " ++ show y
                            
                    mv <- selMove
                    
                    playloop $ boards !! mv

-- |Creates a game and attempts to solve it.  The solver is rudimentary.
solveRandomGame :: IO ()
solveRandomGame = do
    x <- makeGame
    print x
    
    let j = treeSolverPruned x
    
    writeFile "out.txt" (show x ++ show j)
    
    print j

-- |A generic list function that was necessary.
applyAt :: [a] -> Int -> (a->a) -> [a]
applyAt list num f = 
    case after of
        x : xs -> before ++ [f x] ++ xs
        []     -> before

  where
    (before, after) = splitAt num list
