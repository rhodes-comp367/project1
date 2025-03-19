module App where

open import Agda.Builtin.Char
  using (Char)
open import Agda.Builtin.IO
  using (IO)
open import Agda.Builtin.List
  using (List)
open import Agda.Builtin.Maybe
  using (Maybe; just; nothing)
open import Agda.Builtin.Nat
  using (Nat; suc; zero)
open import Agda.Builtin.String
  using (String)
open import Agda.Builtin.Unit
  using (⊤)
open import Fin
  using (Fin; suc; zero)
open import Product
  using (_×_; _,_)

postulate
  Gen
    : Set
  print : String
    → IO ⊤

data Event : Set where
  up
    : Event
  down
    : Event
  left
    : Event
  right
    : Event
  tick
    : Event

record App : Set₁ where
  constructor
    app
  field
    State
      : Set
    initial : Gen
      → State
    draw : State
      → List (List Char)
    handle : Event → State
      → State

-- don't use these functions directly.
module Internal where
  postulate
    gen-nat : Nat → Gen
      → Nat × Gen
    undefined : ∀ {A : Set}
      → A
    run-brick : ∀ {S : Set} → Nat → (Gen → S) → (S → List (List Char)) → (Event → S → S)
      → IO ⊤

from-nat : ∀ n → Nat
  → Maybe (Fin n)
from-nat zero _
  = nothing
from-nat (suc n) zero
  = just zero
from-nat (suc n) (suc k)
  with from-nat n k
... | nothing
  = nothing
... | just l
  = just (suc l)

-- randomly generate a Fin value; return the new generator.
gen-fin : ∀ {n} → Gen
  → Fin (suc n) × Gen
gen-fin {n} g
  with Internal.gen-nat (suc n) g
... | k , g
  with from-nat (suc n) k
... | nothing
  = Internal.undefined
... | just l
  = l , g

-- first argument is time between ticks in microseconds.
run : Nat → App
  → IO ⊤
run n (app _ i d h)
  = Internal.run-brick n i d h

{-# FOREIGN GHC
  import Brick.AttrMap
    (AttrMap, forceAttrMap)
  import Brick.BChan
    (newBChan, writeBChan)
  import Brick.Main
    (App(..), customMain, halt)
  import Brick.Types
    (BrickEvent(..), CursorLocation, EventM, Widget)
  import Brick.Widgets.Border
    (border)
  import Brick.Widgets.Core
    (hBox, str, vBox)
  import Control.Concurrent
    (forkIO, threadDelay)
  import Control.Monad
    (forever)
  import Control.Monad.State.Class
    (modify)
  import qualified Data.Text.IO
    as T
  import Graphics.Vty
    (Vty)
  import Graphics.Vty.Attributes
    (defAttr)
  import Graphics.Vty.Config
    (defaultConfig)
  import qualified Graphics.Vty.Input.Events
    as E
  import Graphics.Vty.Platform.Unix
    (mkVty)
  import System.Random
    (StdGen, initStdGen)
  import Prelude
    hiding (Left, Right)

  genNat :: Integer -> StdGen
    -> (Integer, StdGen)
  genNat
    = undefined

  data Event
    = Up | Down | Left | Right | Tick

  char :: Char
    -> Widget ()
  char
    = str . (: [])

  row :: [Char]
    -> Widget ()
  row
    = hBox . fmap char

  grid :: [[Char]]
    -> Widget ()
  grid
    = vBox . fmap row

  draw :: (s -> [[Char]]) -> s
    -> [Widget ()]
  draw d
    = (: []) . border . grid . d

  cursor :: s -> [CursorLocation ()]
    -> Maybe (CursorLocation ())
  cursor _ _
    = Nothing

  handle :: (Event -> s -> s) -> BrickEvent () ()
    -> EventM () s ()
  handle _ (VtyEvent (E.EvKey E.KEsc _))
    = halt
  handle h (VtyEvent (E.EvKey E.KUp _))
    = modify (h Up)
  handle h (VtyEvent (E.EvKey E.KDown _))
    = modify (h Down)
  handle h (VtyEvent (E.EvKey E.KLeft _))
    = modify (h Left)
  handle h (VtyEvent (E.EvKey E.KRight _))
    = modify (h Right)
  handle h (AppEvent _)
    = modify (h Tick)
  handle _ _
    = modify id

  start
    :: EventM () s ()
  start
    = modify id

  attrs :: s
    -> AttrMap
  attrs _
    = forceAttrMap defAttr

  runBrick :: Integer -> (StdGen -> s) -> (s -> [[Char]]) -> (Event -> s -> s)
    -> IO ()
  runBrick n i d h = do
    vty
      <- mkVty defaultConfig
    chan
      <- newBChan 10
    _
      <- forkIO (forever (writeBChan chan () >> threadDelay (fromIntegral n)))
    app
      <- pure (App (draw d) cursor (handle h) start attrs)
    gen
      <- initStdGen
    _
      <- customMain vty (mkVty defaultConfig) (Just chan) app (i gen)
    pure ()
#-}

{-# COMPILE GHC Event
  = data Event (Up | Down | Left | Right | Tick) #-}
{-# COMPILE GHC Gen
  = type StdGen #-}
{-# COMPILE GHC Internal.gen-nat
  = genNat #-}
{-# COMPILE GHC Internal.run-brick
  = \_ -> runBrick #-}
{-# COMPILE GHC Internal.undefined
  = \_ -> undefined #-}
{-# COMPILE GHC print
  = T.putStrLn #-}

