{-# OPTIONS --cumulativity #-}
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Relation.Nullary
-- for universe levels
open import Agda.Primitive
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Bool

i = lsuc (lsuc (lsuc (lsuc lzero))) -- type level 4
j = lsuc i -- type level 1+i
mutual
  data Context1 : Set j where
    ∅ : Context1
    _,_ : (ctx : Context1) → (ctxType1 ctx → Set i) → Context1

  data Context2 : Context1 → Set j where
    ∅ : ∀{Γ1} → Context2 Γ1
    _,_ : ∀{Γ1} → (ctx : Context2 Γ1) → ((γ : ctxType1 Γ1) → ctxType2 γ ctx → Set i)
      → Context2 Γ1


  -- outputs a type representing the information contained in the context
  ctxType1 : Context1 → Set j
  ctxType1 ∅ = ⊤
  ctxType1 (ctx , h) = Σ (ctxType1 ctx) (λ t → h t)

  ctxType2 : ∀{Γ1} → ctxType1 Γ1 → Context2 Γ1 → Set j
  ctxType2 γ ∅ = ⊤
  ctxType2 γ (ctx , h) = Σ (ctxType2 γ ctx) (λ t → h γ t)

  Context : Set j
  Context = Σ Context1 (λ Γ1 → Context2 Γ1)

  ctxType : Context → Set j
  ctxType (Γ1 , Γ2) = Σ (ctxType1 Γ1) (λ γ → ctxType2 γ Γ2)

  _,,_ : (ctx : Context) → (ctxType ctx → Set i) → Context
  (Γ1 , Γ2) ,, T = Γ1 , Γ2 , (λ γ₁ γ₂ → T (γ₁ , γ₂))

  _,,,_ : ∀{Γ} → {T : ctxType Γ → Set i} → (γ : ctxType Γ)
    → T γ → ctxType (Γ ,, T)
  (γ₁ , γ₂) ,,, t = γ₁ , γ₂ , t


  data InCtx1 : Context1 → Set j where
    same : ∀{Γ T} → InCtx1 (Γ , T)
    next : ∀{Γ T} → InCtx1 Γ → InCtx1 (Γ , T)

  data InCtx2 : ∀{Γ1} → Context2 Γ1 → Set j where
    same : ∀{Γ1 Γ T} → InCtx2 {Γ1} (Γ , T)
    next : ∀{Γ1 Γ T} → InCtx2 {Γ1} Γ → InCtx2 (Γ , T)

  InCtx : Context → Set j
  InCtx (Γ1 , Γ2) = (InCtx1 Γ1) ⊎ (InCtx2 Γ2)

  data InCtx1Type : Context1 → Set j where
    same : ∀{Γ} → InCtx1Type (Γ , λ _ → Set)
    next : ∀{Γ T} → InCtx1Type Γ → InCtx1Type (Γ , T)

  data InCtx2Type : ∀{Γ1} → Context2 Γ1 → Set j where
    same : ∀{Γ1 Γ} → InCtx2Type {Γ1} (Γ , λ _ _ → Set)
    next : ∀{Γ1 Γ T} → InCtx2Type {Γ1} Γ → InCtx2Type (Γ , T)

  InCtxType : Context → Set j
  InCtxType (Γ1 , Γ2) = (InCtx1Type Γ1) ⊎ (InCtx2Type Γ2)

  TypeAt1 : ∀{Γ} → (icx : InCtx1 Γ) → (ctxType1 Γ → Set i)
  TypeAt1 {(_ , T)} same (γ , _) = T γ
  TypeAt1 {.(_ , _)} (next icx) (γ , _) = TypeAt1 icx γ

  TypeAt2 : ∀{Γ1 Γ} → (icx : InCtx2 {Γ1} Γ) → (γ : ctxType1 Γ1)
    → (ctxType2 γ Γ → Set i)
  TypeAt2 {_} {(_ , T)} same γ₁ (γ , _) = T γ₁ γ
  TypeAt2 {_} {.(_ , _)} (next icx) γ₁ (γ , _) = TypeAt2 icx γ₁ γ

  TypeAt : ∀{Γ} → (icx : InCtx Γ) → (ctxType Γ → Set i)
  TypeAt (inj₁ icx) (γ₁ , γ₂) = TypeAt1 icx γ₁
  TypeAt (inj₂ icx) (γ₁ , γ₂) = TypeAt2 icx γ₁ γ₂

  proj1 : ∀{Γ} → (icx : InCtx1 Γ) → (γ : ctxType1 Γ) → TypeAt1 icx γ
  proj1 same (γ , t) = t
  proj1 (next icx) (γ , _) = proj1 icx γ

  proj2 : ∀{Γ1 Γ} → (icx : InCtx2 {Γ1} Γ) → (γ₁ : ctxType1 Γ1)
    → (γ : ctxType2 γ₁ Γ) → TypeAt2 icx γ₁ γ
  proj2 same γ₁ (γ , t) = t
  proj2 (next icx) γ₁ (γ , _) = proj2 icx γ₁ γ

  proj1Type : ∀{Γ} → (icx : InCtx1Type Γ) → (γ : ctxType1 Γ) → Set
  proj1Type same (γ , t) = t
  proj1Type (next icx) (γ , _) = proj1Type icx γ

  proj2Type : ∀{Γ1 Γ} → (icx : InCtx2Type {Γ1} Γ) → (γ₁ : ctxType1 Γ1)
    → (γ : ctxType2 γ₁ Γ) → Set
  proj2Type same γ₁ (γ , t) = t
  proj2Type (next icx) γ₁ (γ , _) = proj2Type icx γ₁ γ

  proj : ∀{Γ} → (icx : InCtx Γ) → (γ : ctxType Γ) → TypeAt icx γ
  proj (inj₁ icx) (γ₁ , γ₂) = proj1 icx γ₁
  proj (inj₂ icx) (γ₁ , γ₂) = proj2 icx γ₁ γ₂

  projType : ∀{Γ} → (icx : InCtxType Γ) → (γ : ctxType Γ) → Set
  projType (inj₁ icx) (γ₁ , γ₂) = proj1Type icx γ₁
  projType (inj₂ icx) (γ₁ , γ₂) = proj2Type icx γ₁ γ₂


mutual
  data V : (Γ : Context) → (ctxType Γ → Set i) → Set j where
    Lambda : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (Γ ,, A) → Set i} →
      V (Γ ,, A) B → V Γ (λ γ → ((x : A γ) → B (γ ,,, x)))
        -- TODO: compare this definition of App with old
    fromU : ∀{Γ T} → U Γ T → V Γ T
    fromType : ∀{Γ} → Type Γ → V Γ (λ _ → Set)
  data U : (Γ : Context) → (ctxType Γ → Set i) → Set j where
    Var : ∀{Γ} → (icx : InCtx Γ)
      → U Γ (λ γ → TypeAt icx γ)
    App : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (Γ ,, A) → Set i} →
        U Γ (λ γ → (a : A γ) → B (γ ,,, a)) → (x : V Γ A) → U Γ (λ γ → B (γ ,,, unqV γ x))
  data Type : (Γ : Context) → Set j where
    Var : ∀{Γ} → (icx : InCtxType Γ) → Type Γ
    Π₀ : {Γ : Context} → (A : Type Γ)
      → (B : Type (Γ ,, (λ γ → unqType γ A)))
      → Type Γ
    _⇒_ : ∀{Γ} → (A B : Type Γ) → Type Γ
    -- Π₁ : {Γ : Context} → (A : Type Γ (λ γ → Set₁))
    --   → (B : V (Γ ,, (λ γ → unqType γ A)) (λ γ → Set₁))
    --   → Type Γ (λ γ → Set₁)
    EBool : ∀{Γ} → Type Γ
    TApp : ∀{Γ A} → Type (Γ ,, A) → V Γ A → Type Γ
    -- Π₀ : {Γ : Context} → (A : Type Γ (λ γ → Set₀))
    --   → (B : V (Γ ,, (λ γ → unqType γ A)) (λ γ → Set₀))
    --   → Type Γ (λ γ → Set₀)
    -- Π₀₁ : {Γ : Context} → (A : Type Γ (λ γ → Set₀))
    --   → (B : V (Γ ,, (λ γ → unqType γ A)) (λ γ → Set₀))
    --   → Type Γ (λ γ → Set₁)
    -- Π₂ : {Γ : Context} → (A : Type Γ (λ γ → Set₂))
    --   → (B : V (Γ ,, (λ γ → unqType γ A)) (λ γ → Set₂))
    --   → Type Γ (λ γ → Set₂)
    -- 𝓤₀ : {Γ : Context} → Type Γ (λ γ → Set₁)
    -- 𝓤₁ : {Γ : Context} → Type Γ (λ γ → Set₂)
    -- 𝓤₂ : {Γ : Context} → Type Γ (λ γ → Set₃)

  -- unquote
  unqV : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → V Γ T → T γ
  unqV γ (Lambda e) = λ x → unqV (γ ,,, x) e
  unqV γ (fromU u) = unqU γ u
  unqV γ (fromType t) = unqType γ t

  unqU : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → U Γ T → T γ
  unqU γ (Var icx) = proj icx γ
  unqU γ (App e₁ e₂) = (unqU γ e₁) (unqV γ e₂)

  unqType : {Γ : Context} → (γ : ctxType Γ) → Type Γ → Set
  unqType γ (Π₀ A B) = (a : unqType γ A) → (unqType (γ ,,, a) B)
  unqType γ (TApp T v) = (unqType (γ ,,, unqV γ v) T)
  unqType γ EBool = Bool
  unqType γ (A ⇒ B) = (unqType γ A) → (unqType γ B)
  unqType γ (Var icx) = projType icx γ
  -- unqType γ (Π₀₁ A B) = (a : unqType γ A) → (unqV (γ ,, a) B)
  -- unqType γ (Π₁ A B) = (a : unqType γ A) → (unqV (γ ,, a) B)
  -- unqType γ (Π₂ A B) = (a : unqType γ A) → (unqV (γ ,, a) B)
  -- unqType γ 𝓤₀ = Set₀
  -- unqType γ 𝓤₁ = Set₁
  -- unqType γ 𝓤₂ = Set₂

_∼_ : {A B : Set} → (A → B) → (A → B) → Set
f ∼ g = (a : _) → f a ≡ g a

inv∼ : {A B : Set} → {f g : A → B} → f ∼ g → g ∼ f
inv∼ p = λ a → sym (p a)

id : {A : Set} → A → A
id a = a
infix 30 _∘_
_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
g ∘ f = λ a → g (f a)
isEquiv : ∀{A B} → (f : A → B) → Set
isEquiv {A} {B} f = (Σ (B → A) (λ g → g ∘ f ∼ id)) × (Σ (B → A) (λ h → f ∘ h ∼ id))
_≃_ : Set → Set → Set
A ≃ B = Σ (A → B) (λ f → isEquiv f)

_⋆_ : ∀{A B} → {f g h : A → B} → f ∼ g → g ∼ h → f ∼ h
p ⋆ q = λ a → trans (p a ) (q a)

inv : ∀{A B} → A ≃ B → B ≃ A
inv (f , (g , pg) , (h , ph))
  = g ∘ (f ∘ h) , ((f , λ a → trans (cong f (pg (h a))) (ph a))
  , (f , λ a → trans (cong g (ph (f a))) (pg a)))

-- IDEA : its not necessary for Exps to be normal form, just split into Exp and Type

ua : ∀{A B Γ2} → (P : Type ((∅ , λ _ → Set) , Γ2))
  → A ≃ B
  → (γA : ctxType2 (tt , A) Γ2)
  → (γB : ctxType2 (tt , B) Γ2)
  → unqType ((tt , A) , γA) P
  → unqType ((tt , B) , γB) P
ua (Π₀ P₁ P₂) eq γA γB x = λ a → ua P₂ eq (γA , ua P₁ (inv eq) γB γA a) (γB , a) (x (ua P₁ (inv eq) γB γA a))
ua (A ⇒ B) eq γA γB x = λ a → ua B eq γA γB (x (ua A (inv eq) γB γA a))
ua EBool eq γA γB x = x
ua {A} {B} (TApp P e) eq γA γB x
  = ua P eq (γA , unqV ((tt , A) , γA) e) (γB , unqV ((tt , B) , γB) e) x
ua (Var (inj₁ same)) eq γA γB x = proj₁ eq x
ua (Var (inj₂ same)) eq γA γB x = {!   !}
ua (Var (inj₂ (next y))) eq γA γB x = {!   !}

-- TODO: IDEA: doesn't leibniz equality imply PropositionalEquality
--  obviously in DSL, not agda itelf because agda can't prove univalence


data Bool2 : Set where
  a : Bool2
  b : Bool2

f : Bool → Bool2
f true = a
f false = b

g : Bool2 → Bool
g a = true
g b = false

lemma1 : f ∘ g ∼ id
lemma1 a = refl
lemma1 b = refl

lemma2 : g ∘ f ∼ id
lemma2 true = refl
lemma2 false = refl


eq : Bool ≃ Bool2
eq = f , (g , lemma2 ) , g , lemma1

--  λ T . T → T
P : Type ((∅ , λ _ → Set) , ∅)
-- P = (Var (inj₁ same)) ⇒ (Var (inj₁ same))
P = Π₀ (Var (inj₁ same)) (Var (inj₁ same))

not1 : Bool → Bool
not1 true = false
not1 false = true

not2 : Bool2 → Bool2
not2 = ua P eq tt tt not1

test1 : not2 a ≡ b
test1 = refl

test2 : not2 b ≡ a
test2 = refl


-- TODO: IDEA: maybe make so that the things in Context2 DONT depend on
-- the things in COntext1?
-- Check Π case!!!!!!!!!!

-- P : Set → Set
-- P T = (n : ℕ) → pow T n

  {-
-- ua2 : ∀{A B} → {e : CtxExt (∅ , λ _ → Set)}
--   → (P : Type (extToCtx e)) → A ≃ B
--   → (γA : ctxExtType e (tt , A))
--   → (γB : ctxExtType e (tt , B))
--   → unqType (pack e (tt , A) γA ) P
--   → unqType (pack e (tt , B) γB ) P
-- ua2 {_} {_} {e} (Π₀ A B) eq γA γB x
--   = λ a → ua2 {_} {_} {cons e {!   !} } B eq {! γA  !} {!   !} {!   !}
-- ua2 (A ⇒ B) eq γA γB x = λ a → ua2 B eq γA γB (x (ua2 A (inv eq) γB γA a))
-- ua2 EBool eq γA γB x = x
-- ua2 (TApp P x₁) eq γA γB x = {!   !}

-- Nothing interesting can be done with only one type level
-- but lets just see what happens?
-- TODO: later rename Type to Type₁, and make Type₂
ua : ∀{A B Γ} → (P : Type (Γ , (λ _ → Set))) → A ≃ B
  → (γ : ctxType Γ)
  → unqType (γ , A) P → unqType (γ , B) P
ua (Π₀ A B) eq γ x = λ a → {! ua B eq   !}
ua (TApp T v) eq γ x = {! rename T  !}
-- TODO: the issue is that B's context is no longer of the right form.
-- the solution is to make contexts not be strictly a list, so that its easy
-- when something is appended, a special element can still be easily accessed.

ua (A ⇒ B) eq γ x = λ a → ua B eq γ (x (ua A (inv eq) γ a))
ua EBool eq γ b = b
-- (b : Bool) → if b then Bool else (Bool → Bool)
-- TODO: add if to Val so that interesting dependent types exist

-- What normal forms actually exist in types?
-- (b : Bool)
-- IDEA: we need ANY expression of type Set to be in Type rather than Value
-- Therefore, Type might need its own App or something?
-- So,    AppT : Type (Γ , A) → Value Γ A → Type Γ

------------------------------------------------------------------
{-
TODAY's dastardly scheme: (rethought out) (now for tommorow...)

1) Make ua so that it can input any Γ whose FIRST element is a Set.
  Derive the necessary algebraic structures to make this work.

2) Fill the the Π case of ua

3) Make a special App constructor for Type. Think about if this creates any
  duplication or problems. Think about how 4) will work

4) Fill in the App case of ua
-}
------------------------------------------------------------------
-}
