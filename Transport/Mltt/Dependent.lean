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

end Transport.Mltt.Dependent
