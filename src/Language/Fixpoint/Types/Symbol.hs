module Language.Fixpoint.Types.Symbol where

class Symbol s where
    -- | Compute the distance between two symbols. Used to suggest alternative symbols.
    symbolDistance :: s -> s -> Int

    -- | Whether the symbol is a dummy symbol.
    isDummySymbol :: s -> Bool

class Symbolic a s where
  symbol :: a -> s

