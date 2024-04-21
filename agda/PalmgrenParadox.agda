------------------------------
-- Palmgren's Paradox for the internal Mahlo universe,
-- where the Internal Mahlo universe is defined as in
-- Setzer Arch. Math. Logic 2000
------------------------------

module PalmgrenParadox where

-- We define falsity as the empty type

data ⊥ : Set where

¬ : Set → Set
¬ X = X → ⊥

-- We define the Internal Mahlo Universe, just closed under
--           ⊥, → and formation of U f₀ f₁
-- It doesn't pass Agda's positivity check, so we switch that off
mutual
  {-# NO_POSITIVITY_CHECK #-}
  data M : Set where
    U'    :  (f₀ : (x₀ : M) → (S x₀ → M) → M)
             (f₁ : (x₀ : M) → (x₁ : S x₀ → M) → S (f₀ x₀ x₁) → M)
             → M
    ⊥'    :  M
    _→'_  :  M → M → M

  S : M → Set
  S (U' f₀ f₁)  = U f₀ f₁
  S ⊥'          =  ⊥
  S (a →' b)   =  S a →   S b

  data U (f₀ : (x₀ : M) → (S x₀ → M) → M)
         (f₁ : (x₀ : M) → (x₁ : S x₀ → M) → S (f₀ x₀ x₁) → M) : Set where
    c0 : (x₀ : U f₀ f₁) → (S (T f₀ f₁ x₀) → U f₀ f₁)
         → U f₀ f₁
    c1 : (x₀ : U f₀ f₁) → (x₁ : (S (T f₀ f₁ x₀) → U f₀ f₁))
         → S (T f₀ f₁ (c0 x₀ x₁))
         → U f₀ f₁

  T : (f₀ : (x₀ : M) → (S x₀ → M) → M)
      (f₁ : (x₀ : M) → (x₁ : S x₀ → M) → S (f₀ x₀ x₁) → M)
      → U f₀ f₁ → M
  T f₀ f₁ (c0 x₀ x₁)   = f₀ (T f₀ f₁ x₀) (λ x₀ → T f₀ f₁ (x₁ x₀))
  T f₀ f₁ (c1 x₀ x₁ t) = f₁ (T f₀ f₁ x₀) (λ x₀ → T f₀ f₁ (x₁ x₀)) t

-- We define the Elimination rules, which Palmgren showed they are inconistent.
-- Note that the rule for U' f₀ f₁  has no induction hypothesis
--   there are different versions of what the induction hypothesis is
-- The proof shows that even without the induction hypothesis the
--   elimination rules are inconsistent.

M-elim : {C : M → Set}
       → (dᵤ : (f₀ : ((x₀ : M) → (S x₀ → M) → M))
             → (f₁ : ((x₀ : M) → (x₁ : S x₀ → M) → S (f₀ x₀ x₁) → M))
             → C (U' f₀ f₁))
       → (d⊥ : C ⊥')
       → (d→ : (x y : M) → C x → C y → C (x  →'  y))
       → (x₀ : M) → C x₀
M-elim dᵤ d⊥ d→ (U' f₀ f₁)  = dᵤ f₀ f₁
M-elim dᵤ d⊥ d→ ⊥'          = d⊥
M-elim dᵤ d⊥ d→ (a →' b)  = d→  a b  (M-elim dᵤ d⊥ d→  a)
                                     (M-elim dᵤ d⊥ d→ b)

dum : {x : M} → S x → M
dum a = ⊥'

dum' : {x : M → M}(x₀ : M) (x₁ : S x₀ → M) → S (x x₀) → M
dum' _ _ _ = ⊥'

ap : M → M → M
ap = M-elim (λ f₀ _ x → f₀ x dum)
            (λ _ → ⊥')
            (λ _ _ _ _ _  → ⊥')

{- we get
ap (U' f g) x =  f x dum
-}

emb : (M → M) → M
emb f = U' (λ u _ → f u) dum'

{- we get
ap (emb f) y = f y
-}

y : (M → M) → M
y k = emb (λ x → k (ap x x))

Y : (M → M) → M
Y k = ap (y k)  (y k)


l : M → M
l x = x →' ⊥'


a : M
a = Y l

A : Set
A = S a

{-
a doesn't normalise
but it should be definitionally equal to a →' ⊥'
A should be definitionally equal to ¬ A
However, because of lack of normalising,
Agda doesn't see this.

However we can prove
p₁  : A → ¬ A
p₂  : ¬ A → A
and this is sufficient to proof the inconsistency.

-}


p₁  : A → ¬ A
p₁  x  =  x

p₂  : ¬ A → A
p₂  x = x

p₃  : ¬ A
p₃  x = p₁ x x

p₄  : A
p₄  = p₂ p₃

inconsistent  : ⊥
inconsistent  = p₃ p₄
