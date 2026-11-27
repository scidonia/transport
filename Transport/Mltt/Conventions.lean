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


theorem vecDep_wellFormed : WellFormedSigFull VecDep_sig := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    simp [VecDep_sig] at hp
    subst p
    exact WellScoped.sort
  · intro i hi
    simp [VecDep_sig] at hi
    subst i
    exact WellScoped.ind (by intro a ha; simp at ha)
  · intro ctor hc
    simp [VecDep_sig] at hc
    rcases hc with rfl | rfl
    · refine ⟨?_, ?_, ?_⟩
      · intro p hp
        simp at hp
      · intro i hi
        simp at hi
        subst i
        exact WellScoped.roll (by intro a ha; simp at ha)
      · intro idxs hidxs t ht
        simp at hidxs
    · refine ⟨?_, ?_, ?_⟩
      · intro p hp
        simp at hp
        rcases hp with rfl | rfl
        · exact WellScoped.ind (by intro a ha; simp at ha)
        · exact WellScoped.var (by simp [VecDep_sig])
      · intro i hi
        simp at hi
        subst i
        exact WellScoped.roll (by
          intro a ha
          simp at ha
          subst a
          exact WellScoped.var (by simp [VecDep_sig]))
      · intro idxs hidxs t ht
        simp at hidxs
        subst idxs
        simp at ht
        subst t
        exact WellScoped.var (by simp [VecDep_sig])

theorem finDep_wellFormed : WellFormedSigFull FinDep_sig := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    simp [FinDep_sig] at hp
  · intro i hi
    simp [FinDep_sig] at hi
    subst i
    exact WellScoped.ind (by intro a ha; simp at ha)
  · intro ctor hc
    simp [FinDep_sig] at hc
    rcases hc with rfl | rfl
    · refine ⟨?_, ?_, ?_⟩
      · intro p hp
        simp at hp
        subst p
        exact WellScoped.ind (by intro a ha; simp at ha)
      · intro i hi
        simp at hi
        subst i
        exact WellScoped.roll (by
          intro a ha
          simp at ha
          subst a
          exact WellScoped.var (by simp [FinDep_sig]))
      · intro idxs hidxs t ht
        simp at hidxs
    · refine ⟨?_, ?_, ?_⟩
      · intro p hp
        simp at hp
        subst p
        exact WellScoped.ind (by intro a ha; simp at ha)
      · intro i hi
        simp at hi
        subst i
        exact WellScoped.roll (by
          intro a ha
          simp at ha
          subst a
          exact WellScoped.var (by simp [FinDep_sig]))
      · intro idxs hidxs t ht
        simp at hidxs
        subst idxs
        simp at ht
        subst t
        exact WellScoped.var (by simp [FinDep_sig])


/-! ### Positivity gate for the full-argument signatures -/

@[simp] theorem occursIndFuel_var (fuel I x : Nat) :
    occursIndFuel fuel I (.var x) = false := by
  cases fuel <;> rfl

@[simp] theorem occursIndFuel_sort (fuel I i : Nat) :
    occursIndFuel fuel I (.sort i) = false := by
  cases fuel <;> rfl

@[simp] theorem occursIndFuel_roll_nil (fuel I c : Nat) :
    occursIndFuel fuel I (.roll 0 c []) = false := by
  cases fuel <;> simp [occursIndFuel]

@[simp] theorem occursIndFuel_roll_var (fuel I c x : Nat) :
    occursIndFuel fuel I (.roll 0 c [.var x]) = false := by
  cases fuel <;> simp [occursIndFuel]

@[simp] theorem occursIndFuel_ind_zero_one (fuel : Nat) :
    occursIndFuel fuel 1 (.ind 0 []) = false := by
  cases fuel <;> simp [occursIndFuel]

@[simp] theorem occursIndFuel_ind_zero_two (fuel : Nat) :
    occursIndFuel fuel 2 (.ind 0 []) = false := by
  cases fuel <;> simp [occursIndFuel]

theorem natDep_strict : strictlyPositive 0 NatDep_sig = true := by
  simp [strictlyPositive, NatDep_sig]

theorem eqDep_strict : strictlyPositive 0 EqDep_sig = true := by
  simp [strictlyPositive, EqDep_sig, occursInd, Tm.size]

theorem vecDep_strict : strictlyPositive 1 VecDep_sig = true := by
  simp [strictlyPositive, VecDep_sig, occursInd, Tm.size]

theorem finDep_strict : strictlyPositive 2 FinDep_sig = true := by
  simp [strictlyPositive, FinDep_sig, occursInd, Tm.size]

theorem natDep_gate : lookupIndStrict [NatDep_sig] 0 = some NatDep_sig := by
  simp [lookupIndStrict, lookupInd, lookup, natDep_strict]

theorem vecDep_gate :
    lookupIndStrict [NatDep_sig, VecDep_sig] 1 = some VecDep_sig := by
  simp [lookupIndStrict, lookupInd, lookup, vecDep_strict]

theorem finDep_gate :
    lookupIndStrict [NatDep_sig, VecDep_sig, FinDep_sig] 2 = some FinDep_sig := by
  simp [lookupIndStrict, lookupInd, lookup, finDep_strict]

theorem eqDep_gate : lookupIndStrict [EqDep_sig] 0 = some EqDep_sig := by
  simp [lookupIndStrict, lookupInd, lookup, eqDep_strict]

end Transport.Mltt.Conventions
