import Transport.Mltt.Scoped

/-!
# Uniform signature convention

The old `Eq_sig` stores constructor result indices in the reversed data-parameter
context (`substParams`).  `HasTypeDep.rollDep` substitutes the **full** argument
list (`substMany args`) into the constructor indices.  This file starts the
signatures for that convention:

* data parameters and indices are telescopes in binding order;
* constructor argument types, recursive index arguments, and constructor result
  indices are scoped by the full argument list;
* `EqDep`, `NatDep`, `VecDep`, and `FinDep` are the first signatures.
-/

namespace Transport.Mltt.Conventions

open Transport.Mltt
open Transport.Mltt.Scoped

/-- The telescope invariant for the full-argument convention.  Constructor
result indices are scoped by the full argument list, not only the data
parameters. -/
def WellFormedSigFull (sig : IndSig) : Prop :=
  (∀ p ∈ sig.params, WellScoped sig.params.length p)
    ∧ (∀ i ∈ sig.indices, WellScoped sig.params.length i)
    ∧ ∀ ctor ∈ sig.ctors,
        (∀ p ∈ ctor.paramTys,
          WellScoped
            (sig.params.length + ctor.paramTys.length + ctor.recArgs.length) p)
          ∧ (∀ i ∈ ctor.indices,
              WellScoped
                (sig.params.length + ctor.paramTys.length + ctor.recArgs.length) i)
          ∧ ∀ idxs ∈ ctor.recArgs, ∀ t ∈ idxs,
              WellScoped
                (sig.params.length + ctor.paramTys.length + ctor.recArgs.length) t

def NatDep_sig : IndSig where
  params := []
  indices := []
  level := 0
  ctors := [
    { paramTys := [], recArgs := [], indices := [] },
    { paramTys := [], recArgs := [[]], indices := [] }
  ]

/-- `Vec A : Nat -> Type`; `cons n a v : Vec A (suc n)`. -/
def VecDep_sig : IndSig where
  params := [.sort 0]
  indices := [.ind 0 []]
  level := 0
  ctors := [
    { paramTys := [], recArgs := [], indices := [.roll 0 0 []] },
    { paramTys := [.ind 0 [], .var 0], recArgs := [[.var 1]],
      indices := [.roll 0 1 [.var 1]] }
  ]

/-- `Fin : Nat -> Type`; `fzero n : Fin (suc n)`, `fsucc n i : Fin (suc n)`. -/
def FinDep_sig : IndSig where
  params := []
  indices := [.ind 0 []]
  level := 0
  ctors := [
    { paramTys := [.ind 0 []], recArgs := [],
      indices := [.roll 0 1 [.var 0]] },
    { paramTys := [.ind 0 []], recArgs := [[.var 0]],
      indices := [.roll 0 1 [.var 0]] }
  ]

/-- `Eq A x y` with `refl A x : Eq A x x`.  The result index is `x` (the second
data parameter), under the full-argument convention. -/
def EqDep_sig : IndSig where
  params := [.sort 0, .var 0]
  indices := [.var 1]
  level := 1
  ctors := [
    { paramTys := [], recArgs := [], indices := [.var 1] }
  ]

theorem natDep_wellFormed : WellFormedSigFull NatDep_sig := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    simp [NatDep_sig] at hp
  · intro i hi
    simp [NatDep_sig] at hi
  · intro ctor hc
    simp [NatDep_sig] at hc
    rcases hc with rfl | rfl <;>
      refine ⟨?_, ?_, ?_⟩ <;> simp

theorem eqDep_wellFormed : WellFormedSigFull EqDep_sig := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    simp [EqDep_sig] at hp
    rcases hp with rfl | rfl
    · exact WellScoped.sort
    · exact WellScoped.var (by simp [EqDep_sig])
  · intro i hi
    simp [EqDep_sig] at hi
    subst hi
    exact WellScoped.var (by simp [EqDep_sig])
  · intro ctor hc
    simp [EqDep_sig] at hc
    subst hc
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      simp at hp
    · intro i hi
      simp at hi
      subst hi
      exact WellScoped.var (by simp [EqDep_sig])
    · intro idxs hidxs t ht
      simp at hidxs

end Transport.Mltt.Conventions
