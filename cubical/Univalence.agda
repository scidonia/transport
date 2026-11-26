{-# OPTIONS --cubical --guardedness #-}
module Univalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Data.Bool
open import Cubical.Data.Bool.Properties

-- The existing Cubical Agda library supplies `ua` and its computation rule.
ua-compute : {A B : Type} (e : A ≃ B) (a : A) →
             transport (ua e) a ≡ equivFun e a
ua-compute = uaβ

-- A concrete migration: transport along the univalence path of negation.
not-transport : transport (ua notEquiv) true ≡ false
not-transport = uaβ notEquiv true

-- The univalence path of the identity equivalence is the identity path.
ua-id : ua (idEquiv Bool) ≡ refl
ua-id = uaIdEquiv
