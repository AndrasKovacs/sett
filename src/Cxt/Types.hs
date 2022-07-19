
module Cxt.Types where

import Common
import Syntax
import Values
import NameTable

data Cxt      = Cxt Lvl Env Locals NameTable
type CxtArg a = LvlArg => EnvArg => LocalsArg => NameTableArg => a

forceCxt :: CxtArg a -> CxtArg a
forceCxt a = seq ?lvl (seq ?env (seq ?locals (seq ?nameTable a)))
{-# inline forceCxt #-}
