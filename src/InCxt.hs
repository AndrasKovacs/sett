
{-|
Variants of functions which take a local elaboration context as argument.
-}

module InCxt where

import Control.Exception

import Syntax
import Values
import Cxt.Types
import Common
import Errors

import qualified Evaluation as E
import qualified Presyntax as P

--------------------------------------------------------------------------------

elabError :: Cxt -> P.Tm -> Error -> IO a
elabError cxt t err = throwIO $ ErrorInCxt (_locals cxt) t err

eval :: Cxt -> Tm -> Val
eval cxt = E.eval (_lvl cxt) (_env cxt)
{-# inline eval #-}

quote :: Cxt -> UnfoldOpt -> Val -> Tm
quote cxt opt = E.quote (_lvl cxt) opt
{-# inline quote #-}

force :: Cxt -> Val -> IO Val
force cxt = E.force (_lvl cxt)
{-# inline force #-}

forceAll :: Cxt -> Val -> IO Val
forceAll cxt = E.forceAll (_lvl cxt)
{-# inline forceAll #-}
