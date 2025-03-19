module Product where

data _×_ (A B : Set) : Set where
  _,_ : A → B
    → A × B

{-# COMPILE GHC _×_
  = data (,) ((,)) #-}

