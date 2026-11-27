import Std

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

end Transport.Closure
