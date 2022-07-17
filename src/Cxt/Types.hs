
module Cxt.Types where

import Common
import Syntax
import Values
import NameTable

data Cxt    = Cxt Lvl Env Locals NameTable
type CxtArg = (LvlArg, EnvArg, LocalsArg, NameTableArg)
