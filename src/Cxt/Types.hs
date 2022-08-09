
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
  => a

forceCxt :: InCxt a -> InCxt a
forceCxt f = seq ?lvl (seq ?env (seq ?locals (seq ?nameTable f)))
{-# inline forceCxt #-}
