{-# options_ghc -Wno-unused-imports #-}

module Tests where

import MainInteraction
import Common

tParse :: IO ()
tParse = justElab $ unlines [
  "foo : Set := (((Set)))"
  ]

t1 :: IO ()
t1 = justElab $ unlines [
  "idSet : Set -> Set := λ x. x"
  ]

t2 :: IO ()
t2 = justElab $ unlines [
    "idSet  : Set -> Set := λ x. x"
  , "idProp : Prop -> Prop := λ x. x"
  ]

t3 :: IO ()
t3 = justElab $ unlines [
  "id : (A : Set) -> A -> A := λ A x. x"
  ]

t4 :: IO ()
t4 = justElab $ unlines [
    "id : {A : Set} -> A -> A := λ x. x"
  , "id2 : Set → Set := λ x. id x"
  ]

t5 :: IO ()
t5 = justElab $ unlines [
    "Pair : (A B : Set) → A → B → A × B := λ A B a b. (a, b)"
  ]

t6 :: IO ()
t6 = justElab $ unlines [
    "foo : (A : Set) × A → Set := λ x. x.A"
  ]

t7 :: IO ()
t7 = justElab $ unlines [
    "Graph : Set := (V : Set) × (E : V → V → Set) × ⊤"
  , "foo : (G : Graph) → G.V → G.V → Set := λ g. g.E"
  ]

t8 :: IO ()
t8 = justElab $ unlines [
    "fst : {A : Set}{B : A → Set} → (a : A) × B a → A := λ x. x.1"
  , "snd : {A : Set}{B : A → Set} → (x : (a : A) × B a) → B (fst x) := λ x. x.2"
  ]

t9 :: IO ()
t9 = justElab $ unlines [
  "Eq : (A : Set) → A → A → Set",
  "  := λ A x y. (P : A → Set) → P x → P y",
  "",
  "Refl : (A : Set)(x : A) → Eq A x x",
  "  := λ A x P px. px",
  "",
  "test1 : ⊤ :=",
  "  let m : Set → Set",
  "      := _;",
  "  let p : (A : Set) → (P : Set → Set) → P (m A) → P A",
  "       := λ A P px. px;",
  "  tt",
  "",
  "test2 : ⊤ :=",
  "  let m : (A : Set)(B : A → Set)(a : A)(b : B a) → Set",
  "   := _;",
  "  let p : (A : Set)(B : A → Set)(a : A)(b : B a) → Eq Set (m A B a b) A",
  "   := λ A B a b. Refl Set A;",
  "  tt",
  "",
  "test3 : ⊤ :=",
  "  let m : (A : Set)(B : A → Set)(x : (a : A) × B a) → Set := _;",
  "  let p : (A : Set)(B : A → Set)(x : (a : A) × B a) → Eq Set (m A B x) A",
  "    := λ A B x. Refl Set A;",
  "  tt"
  ]

t10 :: IO () -- TODO
t10 = justElab $ unlines [
  "Eq : (A : Set) → A → A → Set",
  "  := λ A x y. (P : A → Set) → P x → P y",
  "",
  "Refl : (A : Set)(x : A) → Eq A x x",
  "  := λ A x P px. px",

  "test1 : ⊤ :=",
  "  let m : Set × Set × Set → Set",
  "   := _;",
  "  let p : (A B C : Set) → Eq Set (m (A,B,C)) C",
  "   := λ A B C. Refl Set C; tt",

  "test2 : ⊤ :=",
  "  let m : Set → Set",
  "   := _;",
  "  let p : (A : Set × Set) → Eq Set (m A.1) A.1",
  "   := λ A. Refl Set A.1; tt",

  "test3 := ",
  "  let m : Set × Set → Set",
  "   := _;",
  "  let p : (A : Set × Set) → Eq Set (m (A.1, A.2)) A.2",
  "   := λ A. Refl Set A.2; tt",

  "test4 : ⊤ := ",
  "  let m : (Set → Set) → Set",
  "   := _;",
  "  let p : (f : Set → Set) → Eq Set (m (λ x. f x)) (f Set)",
  "   := λ f. Refl Set (f Set); tt",

  "test5 : ⊤ :=",
  "  let m : (Set → Set → Set) → Set",
  "   := _;",
  "  let p : (f : Set → Set → Set) → Eq Set (m (λ x y. f y x)) (f Set (Set → Set))",
  "   := λ f. Refl Set (f Set (Set → Set));",
  "  tt",

  "test6 : ⊤ :=",
  "  let m : Set × Set",
  "   := _;",
  "  let p : Eq Set m.1 Set := Refl Set Set; ",
  "  tt",

  "test7 : (x y : ⊤) → _ = y → x = y := λ x y p. p"
  ]


tFreeze :: IO ()
tFreeze = justElab $ unlines [
  "m : Set := _",
  "",
  "p : m = Set := refl"
  ]


t11 :: IO ()
t11 = justElab $ unlines [
  "testrefl : (A : Set)(x : A) → x = x",
  "  := λ A x. refl"
  ]

t12 :: IO ()
t12 = justElab $ unlines [
  "mysym : (A : Set)(x y : A)(p : x = y) → y = x",
  "  :=  λ A x y p. sym p",

  "id : (A : Set)(x y : A)(p : x = y) → x = y",
  "  :=  λ A x y p. p"
  ]

t13 :: IO ()
t13 = justElab $ unlines [
  -- "foo : Set = Set → Set = Set",
  -- "  := λ p. sym {Set}{Set}{Set} p",
  -- "foo : Set = Set → Set = Set",
  -- "  := sym",
  "foo : Set = Set → ⊤",
  "  := sym"

  ]

tCoeCoe3 :: IO ()
tCoeCoe3 = justElab $ unlines [
  "Eq : (A : Set) → A → A → Set",
  "  := λ A x y. x = y",
  "",
  "testcoecoe3 : {A1 A2 C1 C2 : Set} {f : A1 × A2} {r : (A1 × A2) = (C1 × C2)}",
  "  -> Eq (C1 × C2) (coe {A1 × A2} {C1 × C2} r f)",
  "                  (coe {A1} {C1} r.1 f.1, coe {A2} {C2} (r.2 f.1) f.2)",
  "  := λ {A1} {A2} {C1} {C2} {f} {r}. refl {C1 × C2} {coe {A1 × A2} {C1 × C2} r f}"
  ]

t14 :: IO ()
t14 = justElab $ unlines [

  "testrefl : {A : Set} (x : A) → x = x",
  "        := \\x. refl",
  "testid : {A : Set} {x y : A} → x = y → x = y",
  "        := \\p. p",
  "testsym : {A : Set} {x y : A} → x = y → y = x",
  "        := \\p. sym p",
  "testtrans : {A : Set} {x y z : A} → x = y → y = z → x = z",
  "        := \\p q. trans p q",
  "testap : {A B : Set} (f : A → B) {x y : A} (p : x = y) → f x = f y",
  "        := \\f p. ap f p",

  "Eq : (A : Set) → A → A → Prop := λ A x y. x = y",

  "coep : {A B : Prop} → A = B → A → B := λ {A}{B} p x. coe {A}{B} p x",

  "trp : {A : Set}(B : A → Prop){x y} → x = y → B x → B y := λ B p bx. coep (ap B p) bx",

  "testsymeq : {A : Set} {x y : A} → x = y → (x = x) = (y = x)",
  "          := λ {x:=x} p. ap (λ y. y = x) p",

  "testsym2 : {A : Set} {x y : A} → x = y → y = x",
  "     := λ p. coep (testsymeq p) refl",

  "testcoerefl : {A : Set} {x : A} {p : A = A} -> coe {A} {A} p x = x",
  "            := refl",

  "testcoecoe : {A B C : Set} {x : A} {p : A = B} {q : B = C}",
  "              -> coe {B} {C} q (coe {A} {B} p x) = coe {A} {C} (trans p q) x",
  "           := refl",

  "testfunext : {A B : Set} {f g : A -> B} -> f = g -> ((a : A) -> f a = g a)",
  "        := \\p. p",

  "testcoecoe2 : (A1 A2 C1 C2 : Set)(f : A1 -> A2)(r : (A1 -> A2) = (C1 -> C2))",
  "              → (C1 → C2) := λ A1 A2 C1 C2 f r. coe r f",

  "testcoecoe3 : {A1 A2 B C1 C2 : Set} {f : A1 -> A2} {p : (A1 -> A2) = B} {q : B =",
  "              (C1 -> C2)} {r : (A1 -> A2) = (C1 -> C2)}",
  "            -> coe q (coe p f) = coe r f",
  "            := refl"

  ]

-- propext
t15 :: IO ()
t15 = justElab $ unlines [
  "propext : {P Q : Prop} → (P → Q) → (Q → P) → P = Q := λ f g. (f,g)",
  "idl   : {A : Prop} → (⊤ × A) = A := (λ y. y.2, λ x. (tt, x))",
  "idr   : {A : Prop} → (A × ⊤) = A := (λ y. y.1, λ x. (x, tt))",
  "swapP : {A B : Prop} → A × B → B × A := λ ab. (ab.2, ab.1)",
  "comm  : {A B : Prop} → (A × B) = (B × A) := (swapP, swapP)",
  "ass   : {A B C : Prop} → (A × B × C) = ((A × B) × C) :=",
  "         (λ abc. ((abc.1, abc.2.1), abc.2.2), λ abc. (abc.1.1, abc.1.2, abc.2))"
  ]

t16 :: IO ()
t16 = justElab $ unlines [
  "myRefl : {A x} → x ={A} x := refl"
  ]

tConst = justElab $ unlines [
  "const := λ {A}{B}(x : A) (y : B). x"
  ]

eqProd = justElab $ unlines [
  "eqprod : {A B : Set} {x y : A * B} -> (x = y) = ((x.1 = y.1) * (x.2 = y.2))",
  " := \\{A} {B} {x} {y}. refl {Set} {x = y}"
  ]

coeProd = justElab $ unlines [
  "coeprod : {A1 B1 A2 B2 : Set} (p : (A1 * B1) = (A2 * B2)) {x}",
  "        -> coe {A1 * B1} {A2 * B2} p x = {A2 * B2} (coe {A1} {A2} p.1 x.1 , coe {B1} {B2} (p.2 x.1) x.2)",
  "  := λ p. refl"

  ]

nounfold = justElab $ unlines [
  "Pointed : Set := (type : Set) × (point : type) × ⊤",
  "",
  "foo : (P : Pointed) → P = P",
  "  := λ p. refl  "
  ]

-- implicit multiple lambda binder syntax
-- local name shadowing in printing
-- disallow top shadowing
-- fewer db indices in printed syntax
-- Allow Coq-style definition parameters
-- Syntactic sugar for record construction:
--   (field1 := x, field2 := y, ..., tt)

-- Tagged
-- tests
-- small meta solution inlining
--
-- printing overhaul:
--   options:
--     - toggle meta type printing
--     - toggle inserted implicits printing (TODO: track inserted things)
--     - toggle all implicit printing
--     - toggle irrelevant term printing (we need type-informed printing for this!)
--     - meta zonking
--   where to put options
--     - pragma in files
--     - set from CLI

-- printing options affect all printing including errors


pruneProj = justElab $ unlines [
  "UEq : (A : Set) → A → A → Set",
  "  := λ A x y. (P : A → Set) → P x → P y",
  "",
  "urefl : (A : Set)(x : A) → UEq A x x",
  "  := λ _ _ _ px. px  ",
  "test5 : Set",
  "  := let m1 : Set → Set → Set × Set := _;",
  "     let m2 : Set → Set := _;",
  "     let p  : (A B : Set) → UEq Set (m2 A) ((m1 A B).1 → (m1 A B).1)",
  "            := λ A B. urefl Set (m2 A);",
  "     Set  "
  ]

approxUnify = justElab $ unlines [
  "Nat : Set",
  " := (n : Set) → (n → n) → n → n",
  "",
  "n10 : Nat := λ N s z. s (s (s (s (s (s z)))))",
  "",
  "approxConv  : n10 ={Nat} n10 := refl"
  ]

invertSg = justElab $ unlines [
  "test5 : El ⊤ :=",
  "  let m : (x : (A : Set) × A) → x.1 := _;",
  "  let p : (A : Set)(x : A) → El (m (A, x) ={A} x) := λ A a. refl {A} {a};",
  "  tt  "
  ]


unf = justElab $ unlines [
  "Pointed : Set := (type : Set) × (point : type) × ⊤",
  "Pointed2 : Set := Pointed",
  "",
  "PointedId : (P : Pointed) → P ={Pointed2} P",
  "  := λ p. refl"
  ]

test = justElab $ unlines [
  "id : {A : Set} → A → A",
  " := λ x. x",
  "",
  "comp : {A B C : Set} → (B → C) → (A → B) → A → C",
  " := λ f g x. f (g x)",
  "",
  "Iso : Set → Set → Set",
  " := λ A B. (to    : A → B)",
  "         * (from  : B → A)",
  "         * (efrom : comp {B}{A}{_} to from = id)",
  "         * Top",
  "",
  "foo : (A B : Set) → Iso A A ={Set} Iso A B",
  "  := λ A B. refl {Set}"
  ]


-- unify | comp {A} {A} {?0 A A to from} to from @0 ={?0 A A to from} id {?1 A A to from} @0
--       | comp {?2 A} {A} {?0 A (?2 A) to from} to from @0 ={?0 A (?2 A) to from} id {?1 A (?2 A) to from} @0
--       | USRigid 0 END

nonlinear = justElab $ unlines [
  "test : Top",
  "  := let m : Set -> Set -> Set := _;",
  "     let p : (A : Set) -> m A A ={Set} A := \\A. refl{Set}{A};",
  "     Set"
  ]
