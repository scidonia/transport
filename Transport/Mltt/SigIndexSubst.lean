import Transport.Mltt.SigIndexFull

/-!
# Substituting the full-argument signature indices

`sigTyListFull` and `rollIndexArgsFull` build telescopes by substituting the
whole argument list with `substMany`.  This file shows that those expressions
commute with a substitution `σ` applied to every argument: substituting the
mapped arguments gives the map of the substituted expression.

The hypotheses `WellFormedSigFull sig` scope the family's telescopes, and the
argument-length equations lift those bounds to `args.length`, so
`substMany_subst_of_wellScoped` applies.
-/

namespace Transport.Mltt

open Transport.Mltt.Scoped
open Transport.Mltt.Conventions

theorem sigTyListFull_subst (sig : IndSig) (h : WellFormedSigFull sig)
    (args : List Tm) (hlen : args.length = sig.params.length + sig.indices.length)
    (σ : Nat → Tm) :
    sigTyListFull sig (args.map (Tm.subst σ))
      = (sigTyListFull sig args).map (Tm.subst σ) := by
  unfold sigTyListFull
  rw [List.map_append]
  congr 1
  · rw [List.map_map]
    apply List.map_congr_left
    intro p hp
    have hp' : WellScoped sig.params.length p := h.1 p hp
    have hp'' : WellScoped args.length p := hp'.mono (by omega)
    exact substMany_subst_of_wellScoped σ args p hp''
  · rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    have hi' : WellScoped sig.params.length i := h.2.1 i hi
    have hi'' : WellScoped args.length i := hi'.mono (by omega)
    exact substMany_subst_of_wellScoped σ args i hi''

theorem rollIndexArgsFull_subst (sig : IndSig) (h : WellFormedSigFull sig)
    (ctor : CtorSig) (hc : ctor ∈ sig.ctors) (args : List Tm)
    (hlen : args.length = sig.params.length + ctor.paramTys.length + ctor.recArgs.length)
    (σ : Nat → Tm) :
    rollIndexArgsFull sig ctor (args.map (Tm.subst σ))
      = (rollIndexArgsFull sig ctor args).map (Tm.subst σ) := by
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
    exact substMany_subst_of_wellScoped σ args d hd''

end Transport.Mltt
