import Std

/-!
# Reversal costs

Stage 5 of the research programme.  The cost model counts allocated cons
cells only: `reverse (x :: xs) = reverse xs ++ [x]` costs one cons per element
of the left list at each step, while the accumulator worker costs one cons per
element total.

The exact counts are:

* `2 * reverseCost xs = xs.length * (xs.length + 1)`;
* `revAccCost xs = xs.length`;
* `revAccCost xs ≤ reverseCost xs`.
-/

namespace Transport.Cost

universe u

/-- Cons cells allocated by naïve reverse. -/
def reverseCost {α : Type u} : List α → Nat
  | [] => 0
  | _ :: xs => reverseCost xs + xs.length + 1

/-- Cons cells allocated by the accumulator worker: one per element. -/
def revAccCost {α : Type u} : List α → Nat
  | [] => 0
  | _ :: xs => revAccCost xs + 1

theorem revAccCost_eq_length {α : Type u} (xs : List α) :
    revAccCost xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [revAccCost, ih]

/-- Arithmetic fact used by the quadratic count. -/
theorem succ_mul_succ_succ (n : Nat) :
    (n + 1) * (n + 2) = n * (n + 1) + 2 * (n + 1) := by
  rw [Nat.mul_succ (n + 1) (n + 1)]
  rw [Nat.succ_mul n (n + 1)]
  omega

/-- Naïve reverse allocates the quadratic number of cons cells. -/
theorem two_mul_reverseCost {α : Type u} (xs : List α) :
    2 * reverseCost xs = xs.length * (xs.length + 1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [reverseCost, List.length_cons, succ_mul_succ_succ]
      omega

/-- The accumulator worker is never more expensive than naïve reverse. -/
theorem revAccCost_le_reverseCost {α : Type u} (xs : List α) :
    revAccCost xs ≤ reverseCost xs := by
  induction xs with
  | nil => simp [revAccCost, reverseCost]
  | cons x xs _ =>
      rw [revAccCost, reverseCost, revAccCost_eq_length]
      omega

end Transport.Cost
