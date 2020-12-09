{-# OPTIONS --cumulativity #-}
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Relation.Nullary
-- for universe levels
open import Agda.Primitive
open import Data.Empty
open import Data.Unit

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

  CtxAt : ∀{Γ} → InCtx Γ → Context
  CtxAt {(Γ , _)} same = Γ
  CtxAt {(_ , _)} (next icx) = CtxAt icx

  TypeAt : ∀{Γ} → (icx : InCtx Γ) → (ctxType Γ → Set i)
  TypeAt {(_ , T)} same (γ , _) = T γ
  TypeAt {.(_ , _)} (next icx) (γ , _) = TypeAt icx γ

  proj : ∀{Γ} → (icx : InCtx Γ) → (γ : ctxType Γ) → TypeAt icx γ
  proj same (γ , t) = t
  proj (next icx) (γ , _) = proj icx γ

mutual
  data Exp : (Γ : Context) → (ctxType Γ → Set i) → Set j where
    Lambda : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (Γ , A) → Set i} →
      Exp (Γ , A) B → Exp Γ (λ γ → ((x : A γ) → B (γ , x)))
    Π₀ : {Γ : Context} → (A : Exp Γ (λ γ → Set₀))
      → (B : Exp (Γ , (λ γ → unq γ A)) (λ γ → Set₀))
      → Exp Γ (λ γ → Set₀)
    Π₀₁ : {Γ : Context} → (A : Exp Γ (λ γ → Set₁))
      → (B : Exp (Γ , (λ γ → unq γ A)) (λ γ → Set₀))
      → Exp Γ (λ γ → Set₁)
    Π₁ : {Γ : Context} → (A : Exp Γ (λ γ → Set₁))
      → (B : Exp (Γ , (λ γ → unq γ A)) (λ γ → Set₁))
      → Exp Γ (λ γ → Set₁)
    Π₂ : {Γ : Context} → (A : Exp Γ (λ γ → Set₂))
      → (B : Exp (Γ , (λ γ → unq γ A)) (λ γ → Set₂))
      → Exp Γ (λ γ → Set₂)
    𝓤₀ : {Γ : Context} → Exp Γ (λ γ → Set₁)
    𝓤₁ : {Γ : Context} → Exp Γ (λ γ → Set₂)
    𝓤₂ : {Γ : Context} → Exp Γ (λ γ → Set₃)
    Var : ∀{Γ} → (icx : InCtx Γ)
      → Exp Γ (λ γ → TypeAt icx γ)
    App : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (Γ , A) → Set i} →
        Exp Γ (λ γ → (a : A γ) → B (γ , a)) → (x : Exp Γ A) → Exp Γ (λ γ → B (γ , unq γ x))
        -- TODO: compare this definition of App with old

  -- unquote
  unq : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → Exp Γ T → T γ
  unq γ (Lambda e) = λ x → unq (γ , x) e
  unq γ (Var icx) = proj icx γ
  unq γ (App e₁ e₂) = (unq γ e₁) (unq γ e₂)
  unq γ (Π₀ A B) = (a : unq γ A) → (unq (γ , a) B)
  unq γ (Π₀₁ A B) = (a : unq γ A) → (unq (γ , a) B)
  unq γ (Π₁ A B) = (a : unq γ A) → (unq (γ , a) B)
  unq γ (Π₂ A B) = (a : unq γ A) → (unq (γ , a) B)
  unq γ 𝓤₀ = Set₀
  unq γ 𝓤₁ = Set₁
  unq γ 𝓤₂ = Set₂


  -- Suppose that one could prove the following:
zero : ∀{Γ} → Exp Γ (λ γ → (T : Set) → T → (T → T) → T)
zero = Lambda (Lambda (Lambda (Var (next same))))
-- λ T a f . a

-- TODO: TODO: TODO: a fundamental problem below with this unquoting implementation!!!
-- Somehow the succ program can't be written!

funId : ∀{Γ} → Exp Γ (λ _ → ((T : Set) → T → T → T) → ((T : Set) → T → T → T))
funId = Lambda (Lambda (Lambda (Lambda
  (App (App (App (Var (next (next (next same))))
  (Var (next (next same))) )
  (Var (next same)) )
  (Var same) ))))

succ : ∀{Γ} → Exp Γ
  (λ γ → ((T : Set) → T → (T → T) → T)
  → ((T : Set) → T → (T → T) → T))
succ = Lambda (Lambda (Lambda (Lambda
  (App
    (App
      (App
        (Var (next (next (next same)))) -- n
        (Var (next (next same)))) -- T
      (App
        (Var same)
        (Var (next same)) )) -- a
      (Var same))
  )))
-- λ n T a f . n T a (f a)

Nat : ∀{Γ} → ctxType Γ → Set₂
Nat = λ γ → (T : Set) → T → (T → T) → T

QNat₁ : ∀{Γ} → Exp Γ (λ _ → Set₁)
QNat₁ =
  Π₀₁
    𝓤₀
    (Π₀
      (Var same)
      (Π₀
        (Π₀ (Var (next same)) (Var (next (next same))))
        (Var (next (next same)))))

-- λ n m . n Nat m succ
plus : ∀{Γ} → Exp Γ (λ γ → Nat γ → Nat γ → Nat γ)
plus = {!   !}
  -- App
  --   (App
  --     (App
  --       (App
  --         {! Var (next (next (next (next (next same)))))  !}
  --         {!   !} )
  --       {!   !} )
  --     {!   !} )
  --   {!   !}

size : ∀{Γ₁ Γ₂} → {T : ctxType Γ₁ → Set i} → Exp Γ₁ T
  → Exp Γ₂ (λ γ → (T : Set) → T → (T → T) → T)
size (Lambda e) = App succ (size e)
size (Π₀ e e₁) = App (App plus (size e)) (size e₁)
size (Π₀₁ e e₁) = App (App plus (size e)) (size e₁)
size (Π₁ e e₁) = App (App plus (size e)) (size e₁)
size (Π₂ e e₁) = App (App plus (size e)) (size e₁)
size 𝓤₀ = App succ zero
size 𝓤₁ = App succ zero
size 𝓤₂ = App succ zero
size (Var icx) = App succ zero
size (App e e₁) = App (App plus (size e)) (size e₁)

mutual
  data Exp2 : (Γ : Context) → (ctxType Γ → Set i) → Set j where
    Lambda : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (Γ , A) → Set i} →
      Exp2 (Γ , A) B → Exp2 Γ (λ γ → ((x : A γ) → B (γ , x)))
    Π₀ : {Γ : Context} → (A : Exp2 Γ (λ γ → Set₀))
      → (B : Exp2 (Γ , (λ γ → unq2 γ A)) (λ γ → Set₀))
      → Exp2 Γ (λ γ → Set₀)
    Π₀₁ : {Γ : Context} → (A : Exp2 Γ (λ γ → Set₁))
      → (B : Exp2 (Γ , (λ γ → unq2 γ A)) (λ γ → Set₀))
      → Exp2 Γ (λ γ → Set₁)
    Π₁ : {Γ : Context} → (A : Exp2 Γ (λ γ → Set₁))
      → (B : Exp2 (Γ , (λ γ → unq2 γ A)) (λ γ → Set₁))
      → Exp2 Γ (λ γ → Set₁)
    Π₂ : {Γ : Context} → (A : Exp2 Γ (λ γ → Set₂))
      → (B : Exp2 (Γ , (λ γ → unq2 γ A)) (λ γ → Set₂))
      → Exp2 Γ (λ γ → Set₂)
    𝓤₀ : {Γ : Context} → Exp2 Γ (λ γ → Set₁)
    𝓤₁ : {Γ : Context} → Exp2 Γ (λ γ → Set₂)
    𝓤₂ : {Γ : Context} → Exp2 Γ (λ γ → Set₃)
    Var : ∀{Γ} → (icx : InCtx Γ)
      → Exp2 Γ (λ γ → TypeAt icx γ)
    App : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (Γ , A) → Set i} →
        Exp2 Γ (λ γ → (a : A γ) → B (γ , a)) → (x : Exp2 Γ A) → Exp2 Γ (λ γ → B (γ , unq2 γ x))
    -- Ldn : ∀{Γ} → {T : ctxType Γ → Set i} → Exp2 Γ (λ γ → ¬_ {i} (¬_ {i} (T γ)))
      -- → Exp2 Γ T

  unq2 : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → Exp2 Γ T → T γ
  unq2 γ e = unq γ (convert e)

  convert : ∀{Γ T} → Exp2 Γ T → Exp Γ T
  convert (Lambda e) = Lambda (convert e)
  convert (Π₀ e e₁) = Π₀ (convert e) (convert e₁)
  convert (Π₀₁ e e₁) = Π₀₁ (convert e) (convert e₁)
  convert (Π₁ e e₁) = Π₁ (convert e) (convert e₁)
  convert (Π₂ e e₁) = Π₂ (convert e) (convert e₁)
  convert 𝓤₀ = 𝓤₀
  convert 𝓤₁ = 𝓤₁
  convert 𝓤₂ = 𝓤₂
  convert (Var icx) = Var icx
  convert (App e e₁) = App (convert e) (convert e₁)
  -- convert (Ldn e) = ldn (convert e)
