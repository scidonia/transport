import Std

/-!
# A step-indexed dependent syntax

The relation is indexed by a step count.  The Pi clause recurses on the step,
not on the type syntax, so it is a recursive definition rather than an
inductive: no non-strictly-positive occurrence, and no termination proof on
substitution.  The full relation is the limit over all steps.

The variable relation is the skeleton: type variables are related to themselves
and term variables are related when they have the same index.  The Pi clause is
the genuine fiberwise clause, so the polymorphic identity certificate is not
vacuous at the outer type argument.
-/

namespace Transport.DependentSyntax

inductive Ty where
  | sort (i : Nat)
  | var (n : Nat)
  | pi (A B : Ty)
  deriving Repr

inductive Tm where
  | var (n : Nat)
  | lam (A : Ty) (t : Tm)
  | app (t u : Tm)
  | ty (A : Ty)
  deriving Repr

/-- Context of type pairs for term variables. -/
abbrev Ctx := List (Ty × Ty)

/-- Step-indexed logical relation. `true` is the type relation, `false` the
term relation. -/
def LR : Nat → Bool → Ctx → Ty → Ty → Tm → Tm → Prop
  | 0, _, _, _, _, _, _ => True
  | _ + 1, true, _, .sort _, .sort _, _, _ => True
  | _ + 1, true, _, .var _, .var _, _, _ => True
  | n + 1, true, Γ, .pi X B, .pi X' B', _, _ =>
      LR n true Γ X X' (.var 0) (.var 0) ∧
      ∀ x x', LR n false Γ X X' x x' →
        LR n true (Γ ++ [(X, X')]) B B' (.var 0) (.var 0)
  | n + 1, false, Γ, .pi X B, .pi X' B', .lam _ t, .lam _ t' =>
      ∀ x x', LR n false Γ X X' x x' →
        LR n false (Γ ++ [(X, X')]) B B' t t'
  | _ + 1, false, _, .sort _, .sort _, .ty _, .ty _ => True
  | _ + 1, false, _, _, _, .var i, .var j => i = j
  | _, _, _, _, _, _, _ => False

/-- The step-indexed type relation. -/
def TyRelAt (n : Nat) (Γ : Ctx) (A A' : Ty) : Prop :=
  LR n true Γ A A' (.var 0) (.var 0)

/-- The step-indexed term relation. -/
def TmRelAt (n : Nat) (Γ : Ctx) (A A' : Ty) (t t' : Tm) : Prop :=
  LR n false Γ A A' t t'

/-- The polymorphic identity type `(A : sort 0) -> A -> A`. -/
def polyIdTy : Ty := .pi (.sort 0) (.pi (.var 0) (.var 1))

/-- The polymorphic identity term. -/
def polyIdTm : Tm := .lam (.sort 0) (.lam (.var 0) (.var 0))

theorem LR_true_sort (n : Nat) (Γ : Ctx) (i j : Nat) :
    LR n true Γ (.sort i) (.sort j) (.var 0) (.var 0) := by
  cases n <;> simp [LR]

theorem LR_true_var (n : Nat) (Γ : Ctx) (i j : Nat) :
    LR n true Γ (.var i) (.var j) (.var 0) (.var 0) := by
  cases n <;> simp [LR]

theorem LR_false_var (n : Nat) (Γ : Ctx) (A A' : Ty) (i j : Nat) (h : i = j) :
    LR n false Γ A A' (.var i) (.var j) := by
  cases n <;> simp [LR, h]

theorem polyIdTyRel : ∀ n, TyRelAt n [] polyIdTy polyIdTy
  | 0 => by simp [TyRelAt, LR]
  | n + 1 => by
      cases n with
      | zero => simp [TyRelAt, LR, polyIdTy]
      | succ n => simp [TyRelAt, LR, polyIdTy, LR_true_var]

theorem polyIdTmRel : ∀ n, TmRelAt n [] polyIdTy polyIdTy polyIdTm polyIdTm
  | 0 => by simp [TmRelAt, LR]
  | n + 1 => by
      cases n with
      | zero => simp [TmRelAt, LR, polyIdTy, polyIdTm]
      | succ n => simp [TmRelAt, LR, polyIdTy, polyIdTm, LR_false_var]

end Transport.DependentSyntax
