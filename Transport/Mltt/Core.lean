import Std

/-!
# MLTT core: indexed syntax and typing

This is the syntactic substrate for the transport development.  It is ported
from the `proof-approach` MLTT stage and deliberately differs from
`Scidonia.Cyclic.Syntax.Term` in the Lean examples:

* `ind` carries its parameters and indices;
* `roll` carries all constructor arguments;
* `case` carries a motive `C` that binds the scrutinee, so the result type is
  `subst0 scrut C`, not simply `C`.

The file fixes the syntax, renaming and substitution, signatures, and the
typing judgment over which the transport theorem is stated.
-/

namespace Transport.Mltt

inductive Tm : Type where
  | var : Nat → Tm
  | sort : Nat → Tm
  | pi : Tm → Tm → Tm
  | lam : Tm → Tm → Tm
  | app : Tm → Tm → Tm
  | fix : Tm → Tm → Tm
  | ind : Nat → List Tm → Tm
  | roll : Nat → Nat → List Tm → Tm
  | case : Nat → Nat → Tm → Tm → List Tm → Tm
  deriving Repr

namespace Tm

/-- Look up a branch by constructor index. -/
def branch (brs : List Tm) (c : Nat) : Option Tm :=
  brs[c]?

/-- Structural size, counting every argument and the case motive. -/
def size : Tm → Nat
  | var _ => 1
  | sort _ => 1
  | pi A B => 1 + size A + size B
  | lam A t => 1 + size A + size t
  | app t u => 1 + size t + size u
  | fix A t => 1 + size A + size t
  | ind _ args => 1 + args.foldr (fun u n => size u + n) 0
  | roll _ _ args => 1 + args.foldr (fun u n => size u + n) 0
  | case _ _ scrut C brs =>
      1 + size scrut + size C + brs.foldr (fun u n => size u + n) 0

/-- Rename under a binder. -/
def upRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | x + 1 => ρ x + 1

/-- Rename under `n` binders. -/
def upRenN : Nat → (Nat → Nat) → Nat → Nat
  | 0, ρ => ρ
  | n + 1, ρ => upRen (upRenN n ρ)

/-- Capture-avoiding renaming.  The `case` motive binds its index variables
and the scrutinee. -/
def rename (ρ : Nat → Nat) : Tm → Tm
  | var x => var (ρ x)
  | sort i => sort i
  | pi A B => pi (rename ρ A) (rename (upRen ρ) B)
  | lam A t => lam (rename ρ A) (rename (upRen ρ) t)
  | app t u => app (rename ρ t) (rename ρ u)
  | fix A t => fix (rename ρ A) (rename (upRen ρ) t)
  | ind I args => ind I (args.map (rename ρ))
  | roll I c args => roll I c (args.map (rename ρ))
  | case I n scrut C brs =>
      case I n (rename ρ scrut) (rename (upRenN (n + 1) ρ) C) (brs.map (rename ρ))

/-- Shift free variables `x ≥ c` by `d`. -/
def shiftSub (d c : Nat) : Nat → Nat :=
  fun x => if x < c then x else x + d

def shift (d c : Nat) (t : Tm) : Tm :=
  rename (shiftSub d c) t

/-- Lift a substitution under a binder. -/
def upSub (σ : Nat → Tm) : Nat → Tm
  | 0 => var 0
  | x + 1 => shift 1 0 (σ x)

/-- Lift a substitution under `n` binders. -/
def upSubN : Nat → (Nat → Tm) → Nat → Tm
  | 0, σ => σ
  | n + 1, σ => upSub (upSubN n σ)

/-- Capture-avoiding substitution.  The `case` motive binds its index
variables and the scrutinee. -/
def subst (σ : Nat → Tm) : Tm → Tm
  | var x => σ x
  | sort i => sort i
  | pi A B => pi (subst σ A) (subst (upSub σ) B)
  | lam A t => lam (subst σ A) (subst (upSub σ) t)
  | app t u => app (subst σ t) (subst σ u)
  | fix A t => fix (subst σ A) (subst (upSub σ) t)
  | ind I args => ind I (args.map (subst σ))
  | roll I c args => roll I c (args.map (subst σ))
  | case I n scrut C brs =>
      case I n (subst σ scrut) (subst (upSubN (n + 1) σ) C) (brs.map (subst σ))

/-- Substitute `u` for de Bruijn variable `0`. -/
def subst0 (u : Tm) (t : Tm) : Tm :=
  subst (fun
    | 0 => u
    | x + 1 => var x) t

end Tm

/-- Constructor signature: parameter types, result indices, and the index
arguments of each recursive field. -/
structure CtorSig where
  paramTys : List Tm
  recArgs : List (List Tm)
  indices : List Tm
  deriving Repr

/-- Inductive signature: parameters and indices, plus its constructors. -/
structure IndSig where
  params : List Tm
  indices : List Tm
  level : Nat
  ctors : List CtorSig
  deriving Repr

def lookup {α : Type} (xs : List α) (n : Nat) : Option α :=
  xs[n]?

def lookupInd (env : List IndSig) (I : Nat) : Option IndSig :=
  lookup env I

def lookupCtor (sig : IndSig) (c : Nat) : Option CtorSig :=
  lookup sig.ctors c

/-! ## Strict positivity

The signature shape above is not itself a positivity check.  A family may only
occur recursively through the `recArgs` fields of its constructors.  Occurrences
in the uniform parameters, index types, non-recursive constructor arguments,
result indices, or recursive index arguments are rejected.

`occursIndFuel` is deliberately fuel-bounded.  `occursInd` uses the term's
structural size as fuel, which is an upper bound on the nesting depth of any
occurrence. -/

def occursIndFuel (fuel : Nat) (I : Nat) (t : Tm) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
      match t with
      | .var _ => false
      | .sort _ => false
      | .pi A B => occursIndFuel fuel I A || occursIndFuel fuel I B
      | .lam A t => occursIndFuel fuel I A || occursIndFuel fuel I t
      | .app t u => occursIndFuel fuel I t || occursIndFuel fuel I u
      | .fix A t => occursIndFuel fuel I A || occursIndFuel fuel I t
      | .ind J args =>
          (J == I) || args.any (fun a => occursIndFuel fuel I a)
      | .roll _ _ args =>
          args.any (fun a => occursIndFuel fuel I a)
      | .case _ _ scrut C brs =>
          occursIndFuel fuel I scrut
            || occursIndFuel fuel I C
            || brs.any (fun b => occursIndFuel fuel I b)

def occursInd (I : Nat) (t : Tm) : Bool :=
  occursIndFuel (Tm.size t) I t

/-- A family signature is strictly positive in its own index `I` when the
family occurs nowhere except as a direct recursive field described by
`recArgs`. -/
def strictlyPositive (I : Nat) (sig : IndSig) : Bool :=
  (! sig.params.any (occursInd I))
    && (! sig.indices.any (occursInd I))
    && sig.ctors.all (fun ctor =>
        (! ctor.paramTys.any (occursInd I))
          && (! ctor.indices.any (occursInd I))
          && (! ctor.recArgs.any (fun idxs => idxs.any (occursInd I))))

/-- Lookup that refuses a signature which is not strictly positive. -/
def lookupIndStrict (env : List IndSig) (I : Nat) : Option IndSig :=
  match lookupInd env I with
  | some sig => if strictlyPositive I sig then some sig else none
  | none => none

/-- Environment-level invariant: every looked-up family is strictly positive. -/
def wellFormedEnv (env : List IndSig) : Prop :=
  ∀ (I : Nat) (sig : IndSig),
    lookupInd env I = some sig → strictlyPositive I sig = true

/-! ### Signature examples and the gate -/

def natTy : Tm := .ind 0 []
def zeroTm : Tm := .roll 0 0 []
def succTm (n : Tm) : Tm := .roll 0 1 [n]

def Nat_sig : IndSig where
  params := []
  indices := []
  level := 0
  ctors := [
    { paramTys := [], recArgs := [], indices := [] },
    { paramTys := [], recArgs := [[]], indices := [] }
  ]

def Vec_sig : IndSig where
  params := [.sort 0]
  indices := [natTy]
  level := 1
  ctors := [
    { paramTys := [], recArgs := [], indices := [zeroTm] },
    { paramTys := [natTy, .var 0], recArgs := [[.var 1]], indices := [succTm (.var 1)] }
  ]

def Fin_sig : IndSig where
  params := []
  indices := [natTy]
  level := 1
  ctors := [
    { paramTys := [natTy], recArgs := [], indices := [succTm (.var 0)] },
    { paramTys := [natTy], recArgs := [[.var 0]], indices := [succTm (.var 0)] }
  ]

def Eq_sig : IndSig where
  params := [.sort 0, .var 0]
  indices := [.var 1]
  level := 1
  ctors := [
    { paramTys := [], recArgs := [], indices := [.var 0] }
  ]

/-- A negative occurrence: `I` appears to the left of an arrow in a
non-recursive constructor argument. -/
def Bad_sig : IndSig where
  params := []
  indices := []
  level := 0
  ctors := [
    { paramTys := [.pi (.ind 0 []) (.sort 0)], recArgs := [], indices := [] }
  ]

-- Development checks were run separately; the typing stage consumes
-- `lookupIndStrict`, so the gate is not a proof target here.

/-! ## M0b: typing with index-refining case

This is the first typed stage.  The gate is `lookupIndStrict`; `ty_ind`,
`ty_roll`, and `ty_case` are unavailable for a family that is not strictly
positive.

The `case` motive `C` lives under the family indices and the scrutinee, so its
branch is checked at the constructor's *result indices* and the result is the
motive at the original indices.  The general constructor-argument telescope is
not implemented yet; the first target uses `Eq`, whose `refl` has no arguments.
-/

abbrev Ctx : Type := List Tm
abbrev Env : Type := List IndSig

def ctxExtend (Γ : Ctx) (A : Tm) : Ctx := A :: Γ

def ctxExtendMany (Γ : Ctx) : List Tm → Ctx
  | [] => Γ
  | A :: As =>
      ctxExtendMany (ctxExtend Γ A) (As.map (Tm.shift 1 0))
termination_by As => As.length
decreasing_by
  simp_wf

def ctxLookup : Ctx → Nat → Option Tm
  | [], _ => none
  | A :: _, 0 => some (Tm.shift 1 0 A)
  | _ :: Γ, n + 1 => (ctxLookup Γ n).map (Tm.shift 1 0)

/-- Substitute a list for the first `args.length` variables. -/
def substMany (args : List Tm) (t : Tm) : Tm :=
  Tm.subst (fun x =>
    match args[x]? with
    | some u => u
    | none => Tm.var (x - args.length)) t

/-- Substitute a telescope into a type whose variables are in that telescope's
newest-first de Bruijn order. -/
def substParams (params : List Tm) (t : Tm) : Tm :=
  substMany params.reverse t

/-- Context for a case motive: bind the index types, then bind the scrutinee
at the generic instance over the freshly bound index variables. -/
def caseMotiveCtx (Γ : Ctx) (I : Nat) (sig : IndSig) (params : List Tm) : Ctx :=
  let idxCtx := ctxExtendMany Γ (sig.indices.map (substParams params))
  let n := sig.indices.length
  ctxExtend idxCtx
    (.ind I (params.map (Tm.shift n 0) ++ (List.range n).reverse.map Tm.var))

/-- The first `n` arguments and the rest. -/
def splitAt (n : Nat) (args : List Tm) : List Tm × List Tm :=
  (args.take n, args.drop n)

def eqTy (A x y : Tm) : Tm := .ind 0 [A, x, y]
def refl (A x : Tm) : Tm := .roll 0 0 [A, x]

/-- Pointwise relation on two lists. -/
def Forall2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ Forall2 R as bs
  | _, _ => False

inductive HasType (env : Env) : Ctx → Tm → Tm → Prop
  | var (Γ : Ctx) (x : Nat) (A : Tm) :
      ctxLookup Γ x = some A →
      HasType env Γ (.var x) A
  | sort (Γ : Ctx) (i : Nat) :
      HasType env Γ (.sort i) (.sort (i + 1))
  | pi (Γ : Ctx) (A B : Tm) (i j : Nat) :
      HasType env Γ A (.sort i) →
      HasType env (ctxExtend Γ A) B (.sort j) →
      HasType env Γ (.pi A B) (.sort (Nat.max i j))
  | lam (Γ : Ctx) (A t B : Tm) (i : Nat) :
      HasType env Γ A (.sort i) →
      HasType env (ctxExtend Γ A) t B →
      HasType env Γ (.lam A t) (.pi A B)
  | app (Γ : Ctx) (t u A B : Tm) :
      HasType env Γ t (.pi A B) →
      HasType env Γ u A →
      HasType env Γ (.app t u) (Tm.subst0 u B)
  | ind (Γ : Ctx) (I : Nat) (sig : IndSig) (args : List Tm) :
      lookupIndStrict env I = some sig →
      args.length = sig.params.length + sig.indices.length →
      (∀ (i : Nat) (a A : Tm),
        args[i]? = some a →
        ((sig.params.map (substMany args)) ++
          (sig.indices.map (substParams (args.take sig.params.length))))[i]? = some A →
        HasType env Γ a A) →
      HasType env Γ (.ind I args) (.sort (sig.level + 1))
  | roll (Γ : Ctx) (I : Nat) (sig : IndSig) (c : Nat) (ctor : CtorSig)
      (args : List Tm) :
      lookupIndStrict env I = some sig →
      lookupCtor sig c = some ctor →
      args.length = sig.params.length + ctor.paramTys.length + ctor.recArgs.length →
      (∀ (i : Nat) (a A : Tm),
        (args.take sig.params.length)[i]? = some a →
        (sig.params.map (substMany args))[i]? = some A →
        HasType env Γ a A) →
      (∀ (i : Nat) (a A : Tm),
        ((args.drop sig.params.length).take ctor.paramTys.length)[i]? = some a →
        (ctor.paramTys.map (substMany args))[i]? = some A →
        HasType env Γ a A) →
      (∀ (i : Nat) (r : Tm) (idxs : List Tm),
        ((args.drop sig.params.length).drop ctor.paramTys.length)[i]? = some r →
        ctor.recArgs[i]? = some idxs →
        HasType env Γ r (.ind I (args.take sig.params.length ++ idxs.map (substMany args)))) →
      HasType env Γ (.roll I c args)
        (.ind I (args.take sig.params.length ++
          ctor.indices.map (substParams (args.take sig.params.length))))
  | case (Γ : Ctx) (I : Nat) (n : Nat) (sig : IndSig) (scrut C : Tm) (brs : List Tm) (i : Nat)
      (args : List Tm) :
      lookupIndStrict env I = some sig →
      n = sig.indices.length →
      args.length = sig.params.length + sig.indices.length →
      HasType env Γ scrut (.ind I args) →
      HasType env
        (caseMotiveCtx Γ I sig (args.take sig.params.length))
        C (.sort i) →
      brs.length = sig.ctors.length →
      (∀ (c : Nat) (ctor : CtorSig) (br : Tm),
        lookupCtor sig c = some ctor →
        Tm.branch brs c = some br →
        ctor.paramTys = [] →
        ctor.recArgs = [] →
        HasType env Γ br
          (substMany
            ([.roll I c (args.take sig.params.length)] ++
              (ctor.indices.map (substParams (args.take sig.params.length))).reverse)
            C)) →
      HasType env Γ (.case I n scrut C brs)
        (substMany ([scrut] ++ (args.drop sig.params.length).reverse) C)

/-! ### The Eq/J eliminator

`J A x P d y p = case p of refl => d`, with motive `P y p`.
-/

def ctxJ : Ctx := [
  eqTy (.var 4) (.var 3) (.var 0),
  .var 3,
  .app (.app (.var 0) (.var 1)) (refl (.var 2) (.var 1)),
  .pi (.var 1) (.pi (eqTy (.var 2) (.var 1) (.var 0)) (.sort 0)),
  .var 0,
  .sort 0
]

def jMotive : Tm :=
  .app (.app (.var 5) (.var 1)) (.var 0)

def jTerm : Tm :=
  .case 0 1 (.var 0) jMotive [.var 2]

def jResult : Tm :=
  .app (.app (.var 3) (.var 1)) (.var 0)

def J_has_type : Prop :=
  HasType [Eq_sig] ctxJ jTerm jResult

end Transport.Mltt
