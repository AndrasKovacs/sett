
## TODO infrastructure

- CI: build & test on just one GHC version
- releases in the repo + tags on commits
- version: follow Haskell PVP (necessary if we put it on Hackage (or Stackage))
- TODO DOCS
     - for dev docs: first just docs.md in subfolder + haddock-style
       module docs
	 - user docs: (readthedocs etc.), long term
- SHORT TERM NOTE:
  stack ghci & stack build are not in sync, check that build works

- András: how I build & install
  1. install stack with ghcup
  2. build with "stack build"  or: "stack build --fast"

### Implicit parameters

- There's a plugin for making implicit params strict, but it can only handle
  curried implicit arguments, like `Arg1 => Arg2 => Arg3 => a -> b`. So we want
  to avoid implicit params tupled up.
- If you use an implicit param in a function, write it out in the type signatures.
- The plugin also works on top definitions.
- TODO: make the plugin smarter.
