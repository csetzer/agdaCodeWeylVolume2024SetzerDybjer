------------------------------
-- The internal Mahlo universe following Setzer Arch. Math. Logic 2000
------------------------------

module ExternalMahloUniverse where

-- We define the set of natural numbers and its elimination rule:

data ℕ : Set where
  O  :  ℕ
  s  :  ℕ → ℕ

R : {C : ℕ → Set} → C O → ((n : ℕ) → C n → C (s n)) → (c : ℕ) → C c
R d e O      =  d
R d e (s n)  =  e n (R d e n)


-- Inductive recursive definition of the subuniverses of Set
-- Constructors for closure under standards set formers are omitted

mutual
  data U (f₀ : (X₀ : Set) → (X₀ → Set) → Set)
         (f₁ : (X₀ : Set) → (X₁ : X₀ → Set) → f₀ X₀ X₁ → Set) : Set where
    c₀ : (x₀ : U f₀ f₁)
       → (T f₀ f₁ x₀ → U f₀ f₁)
       → U f₀ f₁
    c₁ : (x₀ : U f₀ f₁)
       → (x₁ : (T f₀ f₁ x₀ → U f₀ f₁))
       → T f₀ f₁ (c₀ x₀ x₁)
       → U f₀ f₁

  T : (f₀ : ((X₀ : Set) → (X₀ → Set) → Set))
      (f₁ : ((X₀ : Set) → (X₁ : X₀ → Set) → f₀ X₀ X₁ → Set))
    → U f₀ f₁ → Set
  T f₀ f₁ (c₀ x₀ x₁)   = f₀ (T f₀ f₁ x₀) (λ z → T f₀ f₁ (x₁ z))
  T f₀ f₁ (c₁ x₀ x₁ t) = f₁ (T f₀ f₁ x₀) (λ z → T f₀ f₁ (x₁ z)) t
