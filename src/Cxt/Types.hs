
module Cxt.Types where

import Common
import Syntax
import Values
import NameTable

type InCxt a =
     LvlArg
  => EnvArg
  => LocalsArg
  => NameTableArg
  => PruningArg
  => a

forceCxt :: InCxt a -> InCxt a
forceCxt a = seq ?lvl (seq ?env (seq ?locals (seq ?nameTable (seq ?pruning a))))
{-# inline forceCxt #-}
