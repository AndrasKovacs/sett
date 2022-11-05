
module Tests where

import MainInteraction

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
  -- , "id2 : Set := id Set"
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
  , "snd : {A : Set}{B : A → Set} → (x : (a : A) × B a) → B (fst {_}{B} x) := λ x. x.2"
  ]

t9 :: IO ()
t9 = justElab $ unlines [
  "Eq : (A : Set) → A → A → Set",
  "  := λ A x y. (P : A → Set) → P x → P y",
  "",
  "Refl : (A : Set)(x : A) → Eq A x x",
  "  := λ A x P px. px",

  -- "m : Set → Set",
  -- "  := _",
  -- "p : (A : Set) → (P : Set → Set) → P (m A) → P A",
  -- "   := λ A P px. px"

  -- "m : (A : Set)(B : A → Set)(a : A)(b : B a) → Set",
  -- " := _",

  -- "p : (A : Set)(B : A → Set)(a : A)(b : B a) → Eq Set (m A B a b) A",
  -- " := λ A B a b. Refl Set A"

  "m : (A : Set)(B : A → Set)(x : (a : A) × B a) → Set",
  " := _",

  "p : (A : Set)(B : A → Set)(x : (a : A) × B a) → Eq Set (m A B x) A",
  " := λ A B x. Refl Set A"
  ]

t10 :: IO () -- TODO
t10 = justElab $ unlines [
  "Eq : (A : Set) → A → A → Set",
  "  := λ A x y. (P : A → Set) → P x → P y",
  "",
  "Refl : (A : Set)(x : A) → Eq A x x",
  "  := λ A x P px. px",

  -- "m : Set × Set × Set → Set",
  -- " := _",

  -- "p : (A B C : Set) → Eq Set (m (A,B,C)) C",
  -- " := λ A B C. Refl Set A"

  -- "m : Set → Set → Set",
  -- " := _",

  -- "p : (A : Set × Set) → Eq Set (m A.1 A.2) A.1",
  -- " := λ A. Refl Set A.1",

  -- "m : Set × Set → Set",
  -- " := _",

  -- "p : (A : Set × Set) → Eq Set (m (A.1, A.2)) A.2",
  -- " := λ A. Refl Set A.1"

  -- "Eq : (A : Set) → A → A → Prop",
  -- "  := λ A x y. x = y;",

  "m : (Set → Set) → Set",
  " := _",

  -- TODO FIX
  "p : (f : Set → Set) → Eq Set (m (λ x. f x)) (f Set)",
  " := λ f. Refl Set (f Set)"

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
t13 = justElab $ unlines [  -- TODO: TraceId unification
  "foo : Set = Set → Set = Set",
  "  := λ (p : Set = Set). sym {Set}{_}{_} p"

  ]


tCoeCoe3 :: IO ()
tCoeCoe3 = justElab $ unlines [
  "Eq : (A : Set) → A → A → Set",
  "  := λ A x y. x = y",
  "",
  "testcoecoe3 : {A1 A2 C1 C2 : Set} {f : A1 × A2} {r : (A1 × A2) = (C1 × C2)}",
  "  -> Eq (C1 × C2) (coe {A1 × A2} {C1 × C2} r f) (coe {A1} {C1} r.1 f.1, coe {A2} {C2} _ f.2)",
  "  := \\{A1} {A2} {C1} {C2} {f} {r}. refl {_} {coe {A1 × A2} {C1 × C2} r f}"
  ]
