import Std
import Transport.ActionRel

/-!
# Positive closures and a higher-order logical relation

`Val` is a strictly positive closure language: `nat` or a syntactic closure over
an environment of values.  Evaluation and application are fuel-indexed; `LR` is
a step-indexed logical relation with a function-space clause.
-/

namespace Transport.Closure

universe u

inductive Ty where
  | nat : Ty
  | arr : Ty → Ty → Ty
  deriving Repr

inductive Tm where
  | var : Nat → Tm
  | zero : Tm
  | succ : Tm → Tm
  | lam : Tm → Tm
  | app : Tm → Tm → Tm

inductive Val where
  | nat : Nat → Val
  | closure : Tm → List Val → Val

def eval : Nat → Tm → List Val → Option Val
  | 0, _, _ => none
  | _ + 1, .var i, env => env[i]?
  | _ + 1, .zero, _ => some (.nat 0)
  | n + 1, .succ t, env =>
      match eval n t env with
      | some (.nat k) => some (.nat (k + 1))
      | _ => none
  | _ + 1, .lam body, env => some (.closure body env)
  | n + 1, .app f a, env =>
      match eval n f env with
      | some (.closure body env') =>
          match eval n a env with
          | some av => eval n body (av :: env')
          | none => none
      | _ => none

def apply : Nat → Val → Val → Option Val
  | 0, _, _ => none
  | n + 1, .closure body env, a => eval n body (a :: env)
  | _ + 1, .nat _, _ => none

def LR : Nat → Ty → Val → Val → Prop
  | 0, _, _, _ => True
  | _ + 1, .nat, .nat a, .nat b => a = b
  | n + 1, .arr A B, f, g =>
      ∀ a b, LR n A a b →
        match apply n f a, apply n g b with
        | some x, some y => LR n B x y
        | _, _ => False
  | _ + 1, _, _, _ => False

example : LR 1 .nat (.nat 0) (.nat 0) := by
  simp [LR]

example : eval 2 (.lam .zero) [] = some (.closure .zero []) := by
  rfl



/-! ## A process/action instance at the closure relation -/

def LRAll (ty : Ty) (v w : Val) : Prop := ∀ n, LR n ty v w

def valueProcess (_ty : Ty) : Transport.Action.Process Val where
  Config := Val
  step := fun _ => none
  obs := fun v => some v

theorem valueBisim {ty : Ty} {v : Val} (h : LRAll ty v v) :
    ∀ n, Transport.ActionRel.BisimRel (LRAll ty)
      (valueProcess ty) (valueProcess ty) n v v := by
  intro n
  cases n with
  | zero => trivial
  | succ n =>
      simpa [Transport.ActionRel.BisimRel, valueProcess] using h

def valueCert (ty : Ty) (v : Val) (h : LRAll ty v v) :
    Transport.ActionRel.DerivationRel (LRAll ty) (valueProcess ty) (valueProcess ty)
      (fun _ => 0) v v :=
  Transport.ActionRel.DerivationRel.cert
    (rel := LRAll ty) (P := valueProcess ty) (Q := valueProcess ty)
    (measure := fun _ => 0) v v (valueBisim h)

theorem valueCert_sound (ty : Ty) (v : Val) (h : LRAll ty v v) :
    ∀ n, Transport.ActionRel.BisimRel (LRAll ty)
      (valueProcess ty) (valueProcess ty) n v v :=
  Transport.ActionRel.DerivationRel.sound (valueCert ty v h)

theorem nat_zero_LRAll : LRAll .nat (.nat 0) (.nat 0) := by
  intro n
  cases n with
  | zero => trivial
  | succ n => simp [LR]

example : Transport.ActionRel.DerivationRel (LRAll .nat)
    (valueProcess .nat) (valueProcess .nat) (fun _ => 0) (.nat 0) (.nat 0) :=
  valueCert .nat (.nat 0) nat_zero_LRAll

end Transport.Closure
