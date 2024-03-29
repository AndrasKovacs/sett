
## SeTT

-- 2022. 07. 08
--------------------------------------------------------------------------------


**Language**:
  - **Haskell**
  - **Strict (language Strict)**

**Libs**:
  - **bytestring**
  - **flatparse, primdata, dynamic-array**
  - **containers (for IntSet + no Hashable req), unordered-containers**
  - **template-haskell**
  -   ? pretty printing, interaction, lsp

**Strings**:
  - **bytestring, String**

Syntax/Lexing/Parsing:
  - problem: operators in record fields
    - Do we want type-informed parsing? (TODO: look at this)

  - we have operators: parsing is scope-dependent
  - **no operators: parsing doesn't depend on anything**

  - if/when we have operators:
    - Agda style fixity/precendence
	    - mixfix precedence parsing without ambiguity
		   (goal: O(N) operator parsing, TODO)

Type system
  - **OTT, closest to Loic & Nicolas**
  - **Strict Prop, ⊤, ⊥, Σ, Π, =, coe, refl, sym, trans, ap,**
    **Set : Set, Prop : Set**
  - **strict coe-refl and coe-trans rule**
  - **local let**
  - **top-level postulates and top-level defs**

  - Prf : Prop → Set
    Prf P := P × sing P

  - **Rafael: Prop ≤ Set**
      - András: don't have subtyping, take max of h-levels in type formers
	            we have h-level metavariables (no abstraction over h-levels)

      - **Rafael: have subtyping, Π Σ are uniform in h-levels
	      +1 András (TODO: work out unification + elab)**

  - abstraction over h-levels?
     Rafael: if we only have uniform Π Σ then we don't have 4 cases, only 2 each

  - universe level (long term):
    - non-first-class levels, polymorphism, _⊔_ in type formers
	- model: level polymorphism in outer 2LTT layer

Records:

 - how first-class?

 - Σ or telescope?

 - 1. **Σ only**
     - **type-directed projection elaboration**
	     example: t : (foo : A) × (bar : B) × ⊤
		          t.foo
				  t.bar
				  (foo, bar, tt)**

     - **magical injectivity annotations**

     - (foo : A) × let myDef = ... in (bar : B) × ⊤   let is not observable from outside
	 - we don't have: definitions + extensions in signatures

	   - example for def in sig:
	     t : Σ(foo : A, bar : B := ..., baz : C)
		 t.bar ≡ (definition)

		 (with Σ only we can redefine myDef externally)

	   - example for extension ("patching") (converts a field into a definition)

         (Σ(foo : A, bar : B, baz : C) | [bar := ...])  (now bar is a definition)

       - cooltt total type coercion?
	      András, Rafael: not keen

    Emulation of nominal records:
      Functor C D := (...., Tag (A, B))   (Tag (C * D)) is the "tag")
	                                       Tag is defn injective, returns in Prop

 - 2. Non-First-class Telescopes
     + Σ( ...   )    ... is always canonical   (very easy to implement)
	                 example: cooltt
     + Identity and coercion probably also easier for these
     - injectivity issue has to be handled
	 - we don't have generic theorems about records

 - 3. First-class telescopes
     + Can abstract over telescopes
	 - (injectivity)
	 - much more complicated

Defn equality control with cofibs:

  "abstract" with more control

  foo : A = ...      -- unfold_foo

  B : Type[unfold_foo => b_rhs] = b_rhs

  bar : B[unfold_foo => rhs] = rhs      -- unfold_bar implies unfold_foo

  representation:
     - I have set of cofs in cxt, closed under implication
	 - during evaluation, I check cof for top unfoldings

  reproduce injectivity annotation:

    Functor C D := functor_def      -- unfold_functor

  (∀ A B. P(Σ A B))

  Alt: injectivity hint: purely for unification

Inductives:
  Basics:
  - non-first-class signatures
  - nominal inductive declarations
  - from each sig, Σ-type of algebras and disp algebras generated
  - primitive rec/elim
  - for an inductive declaration, there's a single telescope of external params

  **infinitary QIIT**

    - **probably: no sort equations**
    - **signatures should be strictly telescope-based (like in Agda)**
	  **every constructor has a telescope of args**
    - **TODO: Id, coe computation **       Id Nat Nat ≡ ⊤,  Id Con Con ≡ ⊤**

  **non-quotient types**

    - **Id: all constructors are disjoint & injective**
	  **(Id/coe computation is primitive)**
    - Future: acyclicity of constructors?      Id (suc n) n ≡ ⊥
    - TODO: Id, coe computation**

  overloaded constructors
    - harder than overloaded fields
	- presyntax should be in spine form so that we can look at overloaded heads

**Modules: copy Agda**
  - module under local defs (lambda-lifted elaboration)?
  - TODO: module instantiation implementation?
     - Everything is defined once, lambda lifted over all
	     enclosing module params
     - Alt: modules are copied on instantiation

	    module N (x : A)(y : B) where
	       foo : A = expensive x y

		   inductive Bar (x : A)(y : A) =
		     c1 : P (foo x y) → P (foo x y) → Barn

	    module M = N arg1 arg2  -->   foo = ...   [x = arg1, y = arg2]
		...
		M.foo = eval N.foo [arg1, arg2]
		...
		M.foo --> <value of foo, possibly closure referring to arg1,arg2>

		M.Bar --> N.Bar arg1 arg2

     - **Rafael: instantiation:
	     - nominal things are lambda lifted
		 - definitions are instantiated**

Overloading:
  - Rust-style impl overloading (projection syntax)
  - if records are *not* nominal, we can't use stupid simple nominal overloading
    (but by-value overloading could be OK)

Elaboration/unification:

  - Uniqueness of unification:
    - **aim for unique choices, but anyway we can't only make unique choices
    - (closer to Agda than Coq)**
    - SProp introduces a bunch of choices anyway

  - Agda-style implicit functions, basic unification
  - Unfolding control:
     **- for all local let-defs?**
     **(local scope is split to controlled/uncontrolled part during eval)**
     - only on top?

  - **TODO: SProp conversion & unification with Rafael type system**
  - **Type-aware unification, eta for ⊤ : Set**

  - Remember that things are computed from Id-s
    - Alternatives:
	  1. Id does not compute definitionally
	  2. Id computes definitionally, but we don't remember anything about Id-s
	  3. Rafael setup:
	     - same as 2, we define a record with an Id field
		 - define primops using wrapped Id args

  - details:
    - postponing, pruning, Σ-unification, postponed λ-insertions
	  postponed overload resolutions
    - eager resumption
	- meta freezing:
	   - metas are only solvable within one top-level def/inductive decl

Rewrite rules
  - defined as case tree + defn equality checks
  - Rafael: extensible conversion checking
  - not just rewrite but also custom conversion rules
     Jesper, Nicolas et al:
	   rewrite rules only refer new constants

     conversion rule:
	   (A : Set)(x : A)(y : A) → ...?

     TODO: how to plug internal eval/conversion in some domain
	       into actual conversion checking?

Long term:
  - coinduction


Ultra long term:
  - internal/external languages
  - full-fledged metatheory of signatures


0th version:
  - Only basic features, no modules, no inductives, no Set/Prop ambiguity



-- 2022. 07. 15
--------------------------------------------------------------------------------

- observation:
  - coe-trans rule + coe->exfalso rule: undecidable
    - coe-exfalso:  coe a b p t --> exfalso b p
    - solution: not have coe->exfalso
	- example: assume inconsistent context (proves ⊥)

      true = coe Bool Bool _ true = coe Nat Bool _ (coe Bool Nat _ true)
	  = exfalso Bool _
	  = ...
	  = false

  - coe-trans rule is quite easy

  - TODO 1: only have coe + Eq in heads, not in spines
  -      2: in printing, print valid field names based on types
  -      3: closures get Lvl as additional arg
  -      4: rename Irrelevant to something (ComputedAway?) (IrrelevantIsh)

 		   <!-- α x =? const x y -->
		   <!-- α := λ x. const x Irrelevant -->

  - Prop ≤ Set  (coercion is El)
  - Design choice: - no Prop/Set ambiguity is allowed in term formers
                   - in Π, Σ, we prefer to elaborate to Prop inhabitants

	 - infer ((x : A) → B)
	         ((x : A) * B)    if h-level is unknown, we postpone (or throw error)

	   - f : (x : A) → B       ty := (A → B) type   -->   El (A → B)
	                           ty := (A → B) type   -->   El A → El B
							     Id ty foo

     <!-- Id Set (El A → El B) (_ → _) = ...
     <!-- Id Set (El (A → B)) (El C)   = Id Prop (A → B) ... (by propext) -->
	     f = .....
  -- goal : single module, basic type formers, field overloding, implicit args, unification

  -- Can we merge conv and unify implementation? (Should we?)
    -- on first approx, should be separate


-- 2022 nov 4
--------------------------------------------------------------------------------

TODO: consider
  - El computes on type formers (coercive Prop <= Set subtyping!)
    - Look at Rafael's mkStrProp construction in implementation
	  (every Set which is def irrelevant is a Prop)
  - Have totally implicit Prop <= Set subtyping
    - Skip El completely
	- Because we have no Set/Prop ambiguity (no H-level metavars)
	  this might not be that awful

  f : A -> Set
  f = \_ -> Top

  f a : Set

  f a ={Set} f a  ≡  Eq Set (f a) (f a)
                  ≡  Eq Prop Top  Top

  f : Prop -> B
  A : Set

  f A

  -- subtyping: implicitly inserts El *and* mkStrProp

  -- Prop ≤ Set
  -- Set -> Prop  (isEmbeddedProp)

  --

  check t Prop
  infer t --> A : Set
  isEmbeddedProp A   (typeRelevance A)

  check t Set
  infer t Prop

  f : Set -> Set
  f A = A

  f Top : Set

  i <= j

  ElB : foo b -> Set
  ElB {true}  A = A
  ElB {false} A = A

  foo : (b : Bool) -> if b then Set else Prop
  ElB (x : foo b) : Set
  foo : ∀ (l : HLevel) → U l
  foo l : U l
