
module Cxt.Types where

import Common
import Syntax
import Values
import NameTable

type CxtArg a =
     LvlArg
  => EnvArg
  => LocalsArg
  => NameTableArg
  => PruningArg
  => a

forceCxt :: CxtArg a -> CxtArg a
forceCxt a = seq ?lvl (seq ?env (seq ?locals (seq ?nameTable (seq ?pruning a))))
{-# inline forceCxt #-}
