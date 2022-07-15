
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
