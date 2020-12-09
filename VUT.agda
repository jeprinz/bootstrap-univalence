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
  data Context : Set j where
    ∅ : Context
    _,_ : (ctx : Context) → (ctxType ctx → Set i) → Context

  -- outputs a type representing the information contained in the context
  ctxType : Context → Set j
  ctxType ∅ = ⊤
  ctxType (ctx , h) = Σ (ctxType ctx) (λ t → h t)

  data InCtx : Context → Set j where
    same : ∀{Γ T} → InCtx (Γ , T)
    next : ∀{Γ T} → InCtx Γ → InCtx (Γ , T)

  data InCtxType : Context → Set j where
    same : ∀{Γ} → InCtxType (Γ , λ _ → Set)
    next : ∀{Γ T} → InCtxType Γ → InCtxType (Γ , T)

  CtxAt : ∀{Γ} → InCtx Γ → Context
  CtxAt {(Γ , _)} same = Γ
  CtxAt {(_ , _)} (next icx) = CtxAt icx

  TypeAt : ∀{Γ} → (icx : InCtx Γ) → (ctxType Γ → Set i)
  TypeAt {(_ , T)} same (γ , _) = T γ
  TypeAt {.(_ , _)} (next icx) (γ , _) = TypeAt icx γ

  proj : ∀{Γ} → (icx : InCtx Γ) → (γ : ctxType Γ) → TypeAt icx γ
  proj same (γ , t) = t
  proj (next icx) (γ , _) = proj icx γ

  projType : ∀{Γ} → (icx : InCtxType Γ) → (γ : ctxType Γ) → Set
  projType same (γ , t) = t
  projType (next icx) (γ , _) = projType icx γ

mutual
  data V : (Γ : Context) → (ctxType Γ → Set i) → Set j where
    Lambda : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (Γ , A) → Set i} →
      V (Γ , A) B → V Γ (λ γ → ((x : A γ) → B (γ , x)))
    fromU : ∀{Γ T} → U Γ T → V Γ T
    fromType : ∀{Γ} → Type Γ → V Γ (λ _ → Set)
  data U : (Γ : Context) → (ctxType Γ → Set i) → Set j where
    Var : ∀{Γ} → (icx : InCtx Γ)
      → U Γ (λ γ → TypeAt icx γ)
    App : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (Γ , A) → Set i} →
        U Γ (λ γ → (a : A γ) → B (γ , a)) → (x : V Γ A) → U Γ (λ γ → B (γ , unqV γ x))
  data Type : (Γ : Context) → Set j where
    Π₀ : {Γ : Context} → (A : Type Γ)
      → (B : Type (Γ , (λ γ → unqType γ A)))
      → Type Γ
    _⇒_ : ∀{Γ} → (A B : Type Γ) → Type Γ
    -- Π₁ : {Γ : Context} → (A : Type Γ (λ γ → Set₁))
    --   → (B : V (Γ , (λ γ → unqType γ A)) (λ γ → Set₁))
    --   → Type Γ (λ γ → Set₁)
    EBool : ∀{Γ} → Type Γ
    Var : ∀{Γ} → (icx : InCtxType Γ) → Type Γ
    -- Π₀ : {Γ : Context} → (A : Type Γ (λ γ → Set₀))
    --   → (B : V (Γ , (λ γ → unqType γ A)) (λ γ → Set₀))
    --   → Type Γ (λ γ → Set₀)
    -- Π₀₁ : {Γ : Context} → (A : Type Γ (λ γ → Set₀))
    --   → (B : V (Γ , (λ γ → unqType γ A)) (λ γ → Set₀))
    --   → Type Γ (λ γ → Set₁)
    -- Π₂ : {Γ : Context} → (A : Type Γ (λ γ → Set₂))
    --   → (B : V (Γ , (λ γ → unqType γ A)) (λ γ → Set₂))
    --   → Type Γ (λ γ → Set₂)
    -- 𝓤₀ : {Γ : Context} → Type Γ (λ γ → Set₁)
    -- 𝓤₁ : {Γ : Context} → Type Γ (λ γ → Set₂)
    -- 𝓤₂ : {Γ : Context} → Type Γ (λ γ → Set₃)

  -- unquote
  unqV : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → V Γ T → T γ
  unqV γ (Lambda e) = λ x → unqV (γ , x) e
  unqV γ (fromU u) = unqU γ u
  unqV γ (fromType t) = unqType γ t

  unqU : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → U Γ T → T γ
  unqU γ (Var icx) = proj icx γ
  unqU γ (App e₁ e₂) = (unqU γ e₁) (unqV γ e₂)

  unqType : {Γ : Context} → (γ : ctxType Γ) → Type Γ → Set
  unqType γ (Π₀ A B) = (a : unqType γ A) → (unqType (γ , a) B)
  unqType γ (Var icx) = projType icx γ
  unqType γ EBool = Bool
  unqType γ (A ⇒ B) = (unqType γ A) → (unqType γ B)
  -- unqType γ (Π₀₁ A B) = (a : unqType γ A) → (unqV (γ , a) B)
  -- unqType γ (Π₁ A B) = (a : unqType γ A) → (unqV (γ , a) B)
  -- unqType γ (Π₂ A B) = (a : unqType γ A) → (unqV (γ , a) B)
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


-- ua : A ≃ B → A = B
-- ua : A ≃ B → (P : Set → Set) → P A → P B
-- ua : (P : Set → Set) → A ≃ B → P A → P B
-- ua : (P : Exp (Set → Set)) → A ≃ B → P A → P B
-- ua : (P : Type [Set] Set) → A ≃ B → P A → P B

-- Nothing interesting can be done with only one type level
-- but lets just see what happens?
-- TODO: later rename Type to Type₁, and make Type₂
ua : ∀{A B} → (P : Type (∅ , (λ _ → Set))) → A ≃ B
  → unqType (tt , A) P → unqType (tt , B) P
ua (Π₀ A B) eq x = λ a → {! ua B eq   !}
ua (Var same) eq x = proj₁ eq x
-- TODO: the issue is that B's context is no longer of the right form.
-- the solution is to make contexts not be strictly a list, so that its easy
-- when something is appended, a special element can still be easily accessed.

-- x : P₁ A → P₂ A
-- return : P₁ B → P₂ B
ua (P₁ ⇒ P₂) eq x = λ a → ua P₂ eq (x (ua P₁ (inv eq) a))
ua EBool eq b = b


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
P : Type (∅ , λ _ → Set)
P = (Var same) ⇒ (Var same)

not1 : Bool → Bool
not1 true = false
not1 false = true

not2 : Bool2 → Bool2
not2 = ua P eq not1

test1 : not2 a ≡ b
test1 = refl

test2 : not2 b ≡ a
test2 = refl


















mutual
  data V2 : (Γ : Context) → (ctxType Γ → Set i) → Set j where
    Lambda : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (Γ , A) → Set i} →
      V2 (Γ , A) B → V2 Γ (λ γ → ((x : A γ) → B (γ , x)))
    fromU : ∀{Γ T} → U2 Γ T → V2 Γ T
    fromType : ∀{Γ} → Type2 Γ → V2 Γ (λ _ → Set)
  data U2 : (Γ : Context) → (ctxType Γ → Set i) → Set j where
    Var : ∀{Γ} → (icx : InCtx Γ)
      → U2 Γ (λ γ → TypeAt icx γ)
    App : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (Γ , A) → Set i} →
        U2 Γ (λ γ → (a : A γ) → B (γ , a)) → (x : V2 Γ A) → U2 Γ (λ γ → B (γ , unqV2 γ x))
  data Type2 : (Γ : Context) → Set j where
    Π₀ : {Γ : Context} → (A : Type2 Γ)
      → (B : Type2 (Γ , (λ γ → unqType2 γ A)))
      → Type2 Γ
    _⇒_ : ∀{Γ} → (A B : Type2 Γ) → Type2 Γ
    EBool : ∀{Γ} → Type2 Γ

  -- unquote
  unqV2 : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → V2 Γ T → T γ
  unqV2 γ (Lambda e) = λ x → unqV2 (γ , x) e
  unqV2 γ (fromU u) = unqU2 γ u
  unqV2 γ (fromType t) = unqType2 γ t

  unqU2 : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → U2 Γ T → T γ
  unqU2 γ (Var icx) = proj icx γ
  unqU2 γ (App e₁ e₂) = (unqU2 γ e₁) (unqV2 γ e₂)

  unqType2 : {Γ : Context} → (γ : ctxType Γ) → Type2 Γ → Set
  unqType2 γ (Π₀ A B) = (a : unqType2 γ A) → (unqType2 (γ , a) B)
  unqType2 γ EBool = Bool
  unqType2 γ (A ⇒ B) = (unqType2 γ A) → (unqType2 γ B)
