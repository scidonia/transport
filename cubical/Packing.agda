{-# OPTIONS --cubical --guardedness #-}
module Packing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Vec
open import Cubical.Data.Vec.Properties

private
  variable
    ℓ : Level
    A : Type ℓ

-- Split a vector at a length.
splitAt : (m : ℕ) {n : ℕ} → Vec A (m + n) → Vec A m × Vec A n
splitAt zero xs = [] , xs
splitAt (suc m) (x ∷ xs) =
  let (ys , zs) = splitAt m xs in (x ∷ ys) , zs

splitAt-++ : (m : ℕ) {n : ℕ} (u : Vec A m) (v : Vec A n) →
             splitAt m (u ++ v) ≡ (u , v)
splitAt-++ zero [] v = refl
splitAt-++ (suc m) (x ∷ u) v =
  cong (λ p → (x ∷ fst p) , snd p) (splitAt-++ m u v)

pack : {m n : ℕ} → Vec A m × Vec A n → Vec A (m + n)
pack (u , v) = u ++ v

pack-split : (m : ℕ) {n : ℕ} (w : Vec A (m + n)) →
             pack (splitAt m w) ≡ w
pack-split zero w = refl
pack-split (suc m) (x ∷ xs) = cong (x ∷_) (pack-split m xs)

splitAt-pack : (m : ℕ) {n : ℕ} (p : Vec A m × Vec A n) →
               splitAt m (pack p) ≡ p
splitAt-pack m (u , v) = splitAt-++ m u v

packIso : (m n : ℕ) → Iso (Vec A m × Vec A n) (Vec A (m + n))
packIso m n = iso pack (splitAt m) (pack-split m) (splitAt-pack m)

packEquiv : (m n : ℕ) → Vec A m × Vec A n ≃ Vec A (m + n)
packEquiv m n = isoToEquiv (packIso m n)

packPath : (m n : ℕ) → Vec A m × Vec A n ≡ Vec A (m + n)
packPath m n = ua (packEquiv m n)

-- Transport along ua computes the packing.
pack-transport : (m n : ℕ) (u : Vec A m) (v : Vec A n) →
                 transport (packPath m n) (u , v) ≡ u ++ v
pack-transport m n u v = uaβ (packEquiv m n) (u , v)

-- Transport backwards computes the splitting.
unpack-transport : (m n : ℕ) (w : Vec A (m + n)) →
                   transport (sym (packPath m n)) w ≡ splitAt m w
unpack-transport m n = ~uaβ (packEquiv m n)

-- The two packing routes agree for dependent clients: the library's
-- append associativity is the required dependent path.
three-vector-coherence :
  {l m n : ℕ} (u : Vec A l) (v : Vec A m) (w : Vec A n) →
  PathP (λ i → Vec A (+-assoc l m n (~ i)))
    ((u ++ v) ++ w) (u ++ (v ++ w))
three-vector-coherence = ++-assoc
