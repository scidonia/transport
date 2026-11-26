import Transport.Cost

/-!
# Queue costs

Stage 5's queue example, at the cons-cell count.  A strict immutable list queue
copies the whole list on every enqueue; the two-list queue conses onto the rear
and reverses it once on refill.

This compares two implementations under the stated cost model.  It is not the
general lower bound: the claim that any linear solution must change the
representation or machine assumptions is a separate argument.
-/

namespace Transport.QueueCost

open Transport.Cost

/-- Cost of one enqueue into a strict list queue of size `n`: copy `n` cells
and allocate one new cell. -/
def strictEnqueueCost (n : Nat) : Nat := n + 1

/-- Total cost of `n` successive enqueues into an empty strict queue. -/
def strictEnqueueTotal : Nat → Nat
  | 0 => 0
  | n + 1 => strictEnqueueTotal n + (n + 1)

/-- The strict queue's total is quadratic. -/
theorem two_mul_strictEnqueueTotal (n : Nat) :
    2 * strictEnqueueTotal n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [strictEnqueueTotal, succ_mul_succ_succ]
      omega

/-- The two-list queue: one cons per enqueue and one reverse per refill, so
`n` enqueues followed by one refill costs `n + n`. -/
def twoListTotalCost (n : Nat) : Nat := n + n

/-- The two-list total is linear. -/
theorem two_list_linear (n : Nat) : twoListTotalCost n = 2 * n := by
  unfold twoListTotalCost
  omega

/-- From three elements on, the two-list total is no worse than the strict
queue's enqueue total. -/
theorem two_list_beats_strict {n : Nat} (hn : 3 ≤ n) :
    twoListTotalCost n ≤ strictEnqueueTotal n := by
  have h2 := two_mul_strictEnqueueTotal n
  have h1 : 2 * twoListTotalCost n = 4 * n := by
    unfold twoListTotalCost
    omega
  have h3 : 4 * n ≤ n * (n + 1) := by
    have h4 : 3 * n ≤ n * n := Nat.mul_le_mul_right n hn
    rw [Nat.mul_succ]
    omega
  omega

end Transport.QueueCost
