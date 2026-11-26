{-# OPTIONS --cubical --guardedness #-}
module Coherence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Vec
open import Cubical.Data.Vec.Properties
open import Packing

private
  variable
    ℓ : Level
    A : Type ℓ

-- Product of equivalences.
prodEquiv : {A B C D : Type ℓ} → A ≃ B → C ≃ D → A × C ≃ B × D
prodEquiv e f =
  isoToEquiv (iso (λ (a , c) → e .fst a , f .fst c)
                  (λ (b , d) → invEq e b , invEq f d)
                  (λ (b , d) i → secEq e b i , secEq f d i)
                  (λ (a , c) i → retEq e a i , retEq f c i))

-- Product associativity.
assocEquiv : {A B C : Type ℓ} → ((A × B) × C) ≃ (A × (B × C))
assocEquiv =
  isoToEquiv (iso (λ ((a , b) , c) → a , (b , c))
                  (λ (a , (b , c)) → (a , b) , c)
                  (λ _ → refl) (λ _ → refl))

module _ {ℓ : Level} {A : Type ℓ} (l m n : ℕ) where
  -- The common domain of both packing routes.
  D : Type ℓ
  D = (Vec A l × Vec A m) × Vec A n

  -- Pack (l,m), then n.
  E1 : D ≃ Vec A ((l + m) + n)
  E1 = compEquiv (prodEquiv (packEquiv l m) (idEquiv (Vec A n)))
                 (packEquiv (l + m) n)

  -- Pack (m,n), then l, with the product associator on the domain.
  E2 : D ≃ Vec A (l + (m + n))
  E2 = compEquiv (compEquiv assocEquiv
                              (prodEquiv (idEquiv (Vec A l)) (packEquiv m n)))
                 (packEquiv l (m + n))

  -- The length path between the two codomains.
  q : Vec A ((l + m) + n) ≡ Vec A (l + (m + n))
  q = cong (Vec A) (sym (+-assoc l m n))

  -- The forward functions agree by append associativity.
  hom : PathP (λ i → D → q i) (E1 .fst) (E2 .fst)
  hom i ((u , v) , w) = ++-assoc u v w i

  -- Lift the function path to a dependent path of equivalences.
  equivPath : PathP (λ i → D ≃ q i) E1 E2
  equivPath = equivPathP hom

  -- The 2-path between the two composite univalence paths.
  two-path : PathP (λ i → D ≡ q i) (ua E1) (ua E2)
  two-path i = ua (equivPath i)
