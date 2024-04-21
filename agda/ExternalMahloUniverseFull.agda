------------------------------
-- The external Mahlo universe with closure under basic set constructions
------------------------------
-- The idea is that "Set" is a Mahlo universe.
-- This means that for each operation F, G on familes of Sets, we can build
-- a "subuniverse" U F G closed under this operation.
-- Since the operation is uniform in F, G, we make the module
-- depend on them as parameters

module ExternalMahloUniverseFull where

open import MonomorphicSets hiding (F;U;T)

-- The line starting with Module indicates that the following is
--   parametrized over F, G:
module _ (F : (A : Set) → (A → Set) → Set)
         (G : (A : Set) → (B : A → Set) → F A B → Set) where
  mutual
    data U : Set where
       n₀ : U
       n₁ : U
       _⊕_ : U → U → U
       σ : (a : U) → (T a → U) → U
       π : (a : U) → (T a → U) → U
       n : U
       w : (a : U) → (T a → U) → U
       i : (a : U) → T a → T a → U
       f : (a : U) → (T a → U) → U
       g : (a : U) → (b : T a → U) → F (T a) (λ x → T (b x)) → U

    T : U → Set
    T n₀        = N₀
    T n₁        = N₁
    T (a ⊕ b)   = T a + T b
    T (σ a b)   = Σ (T a) (λ x → T (b x))
    T (π a b)   = Π (T a) (λ x → T (b x))
    T n         = N
    T (w a b)   = W (T a) (λ x → T (b x))
    T (i a b c) = I (T a) b c
    T (f a b)   = F (T a) (λ x → T (b x))
    T (g a b c) = G (T a) (λ x → T (b x)) c
