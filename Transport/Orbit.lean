import Transport.Mltt.Beta

/-!
# Orbit connectivity

The first milestone of the research programme: connectivity in the graph of an
endofunction, and the beta instance.  The relation is proof-irrelevant here
because it is a statement about which residuals are reachable, not yet a
certificate the client can inspect.

`iter f n x` is the `n`-fold forward iterate of `f` at `x`.  Two points are
orbit-connected when their forward orbits meet.  The relation is an equivalence
for any endofunction, including one with infinite orbits.
-/

namespace Transport.Orbit

universe u

/-- The `n`-fold forward iterate of `f` at `x`. -/
def iter {α : Type u} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (iter f n x)

@[simp] theorem iter_zero {α : Type u} (f : α → α) (x : α) :
    iter f 0 x = x := rfl

@[simp] theorem iter_succ {α : Type u} (f : α → α) (n : Nat) (x : α) :
    iter f (n + 1) x = f (iter f n x) := rfl

/-- Iteration composes on the right: `f^(m+n) = f^m ∘ f^n`. -/
theorem iter_add {α : Type u} (f : α → α) (m n : Nat) (x : α) :
    iter f (m + n) x = iter f m (iter f n x) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_add, iter_succ, ih, iter_succ]

/-- Iteration composes on the left: `f^(m+n) = f^n ∘ f^m`. -/
theorem iter_add' {α : Type u} (f : α → α) (m n : Nat) (x : α) :
    iter f (m + n) x = iter f n (iter f m x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, iter_succ, ih, iter_succ]

/-- A fixed point is fixed by every iterate. -/
theorem iter_fixed {α : Type u} (f : α → α) {x : α}
    (h : f x = x) (n : Nat) : iter f n x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iter_succ, ih, h]

/-- Two points are orbit-connected when their forward orbits intersect. -/
def OrbitConnected {α : Type u} (f : α → α) (p q : α) : Prop :=
  ∃ m n : Nat, iter f m p = iter f n q

theorem orbitConnected_refl {α : Type u} (f : α → α) (p : α) :
    OrbitConnected f p p :=
  ⟨0, 0, rfl⟩

theorem orbitConnected_symm {α : Type u} {f : α → α} {p q : α}
    (h : OrbitConnected f p q) : OrbitConnected f q p := by
  rcases h with ⟨m, n, h⟩
  exact ⟨n, m, h.symm⟩

/-- Meeting points can be shifted along the common orbit, which is what makes
the relation transitive. -/
theorem orbitConnected_trans {α : Type u} {f : α → α} {p q r : α}
    (h1 : OrbitConnected f p q) (h2 : OrbitConnected f q r) :
    OrbitConnected f p r := by
  rcases h1 with ⟨m, n, h1⟩
  rcases h2 with ⟨k, l, h2⟩
  refine ⟨m + k, n + l, ?_⟩
  calc
    iter f (m + k) p = iter f k (iter f m p) := by rw [iter_add']
    _ = iter f k (iter f n q) := by rw [h1]
    _ = iter f (k + n) q := by rw [← iter_add]
    _ = iter f (n + k) q := by rw [Nat.add_comm k n]
    _ = iter f n (iter f k q) := by rw [iter_add]
    _ = iter f n (iter f l r) := by rw [h2]
    _ = iter f (l + n) r := by rw [← iter_add']
    _ = iter f (n + l) r := by rw [Nat.add_comm l n]

theorem orbitConnected_equivalence {α : Type u} (f : α → α) :
    Equivalence (OrbitConnected f) :=
  ⟨orbitConnected_refl f, fun h => orbitConnected_symm h,
    fun h1 h2 => orbitConnected_trans h1 h2⟩

/-- Distinct fixed points are in different components. -/
theorem not_orbitConnected_of_fixed_ne {α : Type u} {f : α → α} {p q : α}
    (hp : f p = p) (hq : f q = q) (hne : p ≠ q) :
    ¬ OrbitConnected f p q := by
  rintro ⟨m, n, h⟩
  rw [iter_fixed f hp m, iter_fixed f hq n] at h
  exact hne h

/-! ## The beta instance -/

namespace BetaInstance

open Transport.Mltt
open Transport.Mltt.Beta

/-- `λx. x` at `sort 0`. -/
def identityTm : Tm := .lam (.sort 0) (.var 0)

/-- `λx. (λy. y) x` at `sort 0`.  The redex is under the outer binder, so the
outermost `beta` does not see it. -/
def redexUnderBinder : Tm :=
  .lam (.sort 0) (.app (.lam (.sort 0) (.var 0)) (.var 0))

@[simp] theorem shift_sort (d c i : Nat) :
    Tm.shift d c (Tm.sort i) = Tm.sort i := by
  simp [Tm.shift, Tm.rename]

@[simp] theorem subst0_sort (u : Tm) (i : Nat) :
    Tm.subst0 u (Tm.sort i) = Tm.sort i := by
  simp [Tm.subst0, Tm.subst]

theorem ctxLookup_sort_zero :
    ctxLookup [Tm.sort 0] 0 = some (Tm.sort 0) := by
  simp [ctxLookup]

theorem ctxLookup_two_sort_zero :
    ctxLookup [Tm.sort 0, Tm.sort 0] 0 = some (Tm.sort 0) := by
  simp [ctxLookup]

theorem hasType_identityTm :
    HasType [] [] identityTm (.pi (.sort 0) (.sort 0)) := by
  refine HasType.lam [] (.sort 0) (.var 0) (.sort 0) 1 ?_ ?_
  · exact HasType.sort [] 0
  · exact HasType.var [.sort 0] 0 (.sort 0) ctxLookup_sort_zero

theorem hasType_redexUnderBinder :
    HasType [] [] redexUnderBinder (.pi (.sort 0) (.sort 0)) := by
  refine HasType.lam [] (.sort 0)
    (.app (.lam (.sort 0) (.var 0)) (.var 0)) (.sort 0) 1 ?_ ?_
  · exact HasType.sort [] 0
  · have hinner : HasType [] [.sort 0] (.lam (.sort 0) (.var 0))
        (.pi (.sort 0) (.sort 0)) := by
      refine HasType.lam [.sort 0] (.sort 0) (.var 0) (.sort 0) 1 ?_ ?_
      · exact HasType.sort [.sort 0] 0
      · exact HasType.var [.sort 0, .sort 0] 0 (.sort 0) ctxLookup_two_sort_zero
    have harg : HasType [] [.sort 0] (.var 0) (.sort 0) :=
      HasType.var [.sort 0] 0 (.sort 0) ctxLookup_sort_zero
    have happ := HasType.app [.sort 0] (.lam (.sort 0) (.var 0)) (.var 0)
      (.sort 0) (.sort 0) hinner harg
    simpa [Tm.subst0, Tm.subst, ctxExtend] using happ

@[simp] theorem beta_fixed_identity : beta identityTm = identityTm := by
  simp [beta, identityTm]

@[simp] theorem beta_fixed_redex : beta redexUnderBinder = redexUnderBinder := by
  simp [beta, redexUnderBinder]

theorem redex_ne_identity : redexUnderBinder ≠ identityTm := by
  intro h
  injection h with _ hbody
  exact Tm.noConfusion hbody

theorem not_orbitConnected_beta :
    ¬ OrbitConnected beta redexUnderBinder identityTm :=
  not_orbitConnected_of_fixed_ne beta_fixed_redex beta_fixed_identity redex_ne_identity

/-- The binder rule the initial calculus lacks: contract the outermost redex of
a lambda body. -/
def betaBinder (t : Tm) : Tm :=
  match t with
  | .lam A body => .lam A (beta body)
  | _ => beta t

@[simp] theorem betaBinder_redex :
    betaBinder redexUnderBinder = identityTm := by
  simp [betaBinder, redexUnderBinder, identityTm, beta, Tm.subst0, Tm.subst]

theorem orbitConnected_betaBinder :
    OrbitConnected betaBinder redexUnderBinder identityTm := by
  refine ⟨1, 0, ?_⟩
  simp [iter, betaBinder_redex]

/-- Stage 1 of the research programme: the two typed fixed points are
disconnected in the initial outermost-beta calculus. -/
theorem typed_fixed_points_disconnected :
    HasType [] [] redexUnderBinder (.pi (.sort 0) (.sort 0)) ∧
    HasType [] [] identityTm (.pi (.sort 0) (.sort 0)) ∧
    ¬ OrbitConnected beta redexUnderBinder identityTm :=
  ⟨hasType_redexUnderBinder, hasType_identityTm, not_orbitConnected_beta⟩

/-- The same two typed fixed points are connected once contraction under a
binder is admitted. -/
theorem typed_fixed_points_connected_after_binder :
    HasType [] [] redexUnderBinder (.pi (.sort 0) (.sort 0)) ∧
    HasType [] [] identityTm (.pi (.sort 0) (.sort 0)) ∧
    OrbitConnected betaBinder redexUnderBinder identityTm :=
  ⟨hasType_redexUnderBinder, hasType_identityTm, orbitConnected_betaBinder⟩

end BetaInstance

end Transport.Orbit
