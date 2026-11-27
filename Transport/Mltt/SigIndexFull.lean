import Transport.Mltt.ScopedSubst
import Transport.Mltt.Conventions

/-!
# Full-argument signature indices

The old `indTyList` and `rollIndexArgs` are `Eq`-specific and substitute only
data parameters.  The full-argument convention scopes constructor result
indices by the whole argument list and substitutes with `substMany args`.

This file defines the general expressions and proves that they commute with
renaming under `WellFormedSigFull`.
-/

namespace Transport.Mltt

open Transport.Mltt.Scoped
open Transport.Mltt.Conventions

/-- Parameter and index telescopes of a family, substituted by the full
argument list. -/
def sigTyListFull (sig : IndSig) (args : List Tm) : List Tm :=
  sig.params.map (substMany args) ++ sig.indices.map (substMany args)

/-- The argument prefix and constructor result indices for a `roll`, under the
full-argument convention. -/
def rollIndexArgsFull (sig : IndSig) (ctor : CtorSig) (args : List Tm) : List Tm :=
  args.take sig.params.length ++ ctor.indices.map (substMany args)

theorem sigTyListFull_rename (sig : IndSig) (h : WellFormedSigFull sig)
    (args : List Tm) (hlen : args.length = sig.params.length + sig.indices.length)
    (ρ : Nat → Nat) :
    sigTyListFull sig (args.map (Tm.rename ρ))
      = (sigTyListFull sig args).map (Tm.rename ρ) := by
  unfold sigTyListFull
  rw [List.map_append]
  congr 1
  · rw [List.map_map]
    apply List.map_congr_left
    intro p hp
    have hp' : WellScoped sig.params.length p := h.1 p hp
    have hp'' : WellScoped args.length p := hp'.mono (by omega)
    exact substMany_rename_of_wellScoped ρ args p hp''
  · rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    have hi' : WellScoped sig.params.length i := h.2.1 i hi
    have hi'' : WellScoped args.length i := hi'.mono (by omega)
    exact substMany_rename_of_wellScoped ρ args i hi''

theorem rollIndexArgsFull_rename (sig : IndSig) (h : WellFormedSigFull sig)
    (ctor : CtorSig) (hc : ctor ∈ sig.ctors) (args : List Tm)
    (hlen : args.length = sig.params.length + ctor.paramTys.length + ctor.recArgs.length)
    (ρ : Nat → Nat) :
    rollIndexArgsFull sig ctor (args.map (Tm.rename ρ))
      = (rollIndexArgsFull sig ctor args).map (Tm.rename ρ) := by
  unfold rollIndexArgsFull
  rw [List.map_append]
  congr 1
  · rw [← List.map_take]
  · rw [List.map_map]
    apply List.map_congr_left
    intro d hd
    have hctor := h.2.2 ctor hc
    have hd' : WellScoped
        (sig.params.length + ctor.paramTys.length + ctor.recArgs.length) d :=
      hctor.2.1 d hd
    have hd'' : WellScoped args.length d := hd'.mono (by omega)
    exact substMany_rename_of_wellScoped ρ args d hd''

end Transport.Mltt
