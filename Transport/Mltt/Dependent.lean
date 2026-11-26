import Transport.Mltt.Core

/-!
# Dependent elimination for indexed families

The core `HasType.case` only eliminates nullary constructors: it requires
`ctor.paramTys = []` and `ctor.recArgs = []`.  This file adds the dependent
case rule for an arbitrary constructor telescope.

The branch context is the constructor's argument telescope
`Δ_i = (ctor.paramTys, ctor.recArgs)`, instantiated at the data parameters.
The branch result is the motive at the constructor's result indices and the
`roll` term, exactly the non-recursive case branch
`Π Δ_i. P u_i (c_i Δ_i)`.

The relation is separate from `HasType` so the existing Eq weakening and beta
proofs keep their current induction.  `ofHasType` embeds the old judgment;
`caseDep` adds the dependent case.  The next stage is weakening/substitution
for `HasTypeDep`.
-/

namespace Transport.Mltt.Dependent

open Transport.Mltt

/-- The constructor arguments as branch variables, in binding order. -/
def branchVars (n : Nat) : List Tm := (List.range n).reverse.map Tm.var

/-- The branch telescope of a constructor at data parameters `params`.
The constructor parameter types are instantiated at `params`; a recursive
field is an `ind I` whose parameter arguments are `params` and whose index
arguments are the constructor's recursive index arguments. -/
def branchTys (I : Nat) (ctor : CtorSig) (params : List Tm) : List Tm :=
  ctor.paramTys.map (substMany params) ++
  ctor.recArgs.map (fun idxs => .ind I (params ++ idxs.map (substMany params)))

/-- The branch context: the constructor telescope under `Γ`. -/
def branchCtx (Γ : Ctx) (I : Nat) (ctor : CtorSig) (params : List Tm) : Ctx :=
  ctxExtendMany Γ (branchTys I ctor params)

/-- The branch result type: the motive at the constructor's result indices
and at the `roll` term built from the data parameters and the branch
variables. -/
def branchTy (I c : Nat) (ctor : CtorSig) (params : List Tm) (C : Tm) : Tm :=
  substMany
    ([.roll I c
        (params ++ branchVars (ctor.paramTys.length + ctor.recArgs.length))]
      ++ (ctor.indices.map (substParams params)).reverse)
    C

/-- Typing with dependent elimination. -/
inductive HasTypeDep (env : Env) : Ctx → Tm → Tm → Prop
  | ofHasType {Γ : Ctx} {t A : Tm} : HasType env Γ t A → HasTypeDep env Γ t A
  | caseDep (Γ : Ctx) (I n : Nat) (sig : IndSig) (scrut C : Tm) (brs : List Tm)
      (i : Nat) (args : List Tm) :
      lookupIndStrict env I = some sig →
      n = sig.indices.length →
      args.length = sig.params.length + sig.indices.length →
      HasTypeDep env Γ scrut (.ind I args) →
      HasTypeDep env
        (caseMotiveCtx Γ I sig (args.take sig.params.length))
        C (.sort i) →
      brs.length = sig.ctors.length →
      (∀ (c : Nat) (ctor : CtorSig) (br : Tm),
        lookupCtor sig c = some ctor →
        Tm.branch brs c = some br →
        HasTypeDep env (branchCtx Γ I ctor (args.take sig.params.length)) br
          (branchTy I c ctor (args.take sig.params.length) C)) →
      HasTypeDep env Γ (.case I n scrut C brs)
        (substMany ([scrut] ++ (args.drop sig.params.length).reverse) C)


/-! ## A dependent case with a constructor parameter

`Unit_sig` has one constructor `c (A : sort 1) : Unit`.  The case below
eliminates it at the constant motive `sort 1`; the branch is a term in the
branch context `[A : sort 1]`.
-/

def Unit_sig : IndSig where
  params := []
  indices := []
  level := 0
  ctors := [
    { paramTys := [.sort 1], recArgs := [], indices := [] }
  ]

def unitVal : Tm := .roll 0 0 [.sort 0]

theorem unitVal_hasType : HasType [Unit_sig] [] unitVal (.ind 0 []) := by
  have hpos : strictlyPositive 0 Unit_sig = true := by
    simp [strictlyPositive, occursInd, occursIndFuel, Tm.size, Unit_sig]
  have hlook : lookupIndStrict [Unit_sig] 0 = some Unit_sig := by
    simp [lookupIndStrict, lookupInd, lookup, hpos]
  refine HasType.roll [] 0 Unit_sig 0 (Unit_sig.ctors[0]) [.sort 0] hlook ?_ ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · intro i a A ha _
    simp [Unit_sig] at ha
  · intro i a A ha hA
    cases i with
    | zero =>
        simp [Unit_sig, substMany, Tm.subst] at ha hA
        subst a
        subst A
        exact HasType.sort [] 0
    | succ i =>
        simp [Unit_sig] at ha
  · intro i r idxs _ hidx
    simp [Unit_sig] at hidx

theorem unit_caseDep :
    HasTypeDep [Unit_sig] []
      (.case 0 0 unitVal (.sort 1) [.sort 0]) (.sort 1) := by
  have hpos : strictlyPositive 0 Unit_sig = true := by
    simp [strictlyPositive, occursInd, occursIndFuel, Tm.size, Unit_sig]
  have hlook : lookupIndStrict [Unit_sig] 0 = some Unit_sig := by
    simp [lookupIndStrict, lookupInd, lookup, hpos]
  simpa [substMany, Tm.subst, Unit_sig] using
    (HasTypeDep.caseDep [] 0 0 Unit_sig unitVal (.sort 1) [.sort 0] 2 []
      hlook rfl rfl
      (HasTypeDep.ofHasType unitVal_hasType)
      (HasTypeDep.ofHasType (HasType.sort (env := [Unit_sig])
        (caseMotiveCtx [] 0 Unit_sig
          (List.take Unit_sig.params.length ([] : List Tm))) 1))
      rfl
      (by
        intro c ctor br hctor hbr
        cases c with
        | zero =>
            simp [Unit_sig, lookupCtor, lookup] at hctor
            subst hctor
            simp [Tm.branch] at hbr
            subst hbr
            simpa [branchCtx, branchTys, branchTy, branchVars, ctxExtendMany, ctxExtend,
              substMany, Tm.subst, Unit_sig]
              using (HasTypeDep.ofHasType (HasType.sort [.sort 1] 0))
        | succ c =>
            simp [Unit_sig, lookupCtor, lookup] at hctor))

end Transport.Mltt.Dependent
