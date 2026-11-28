# Roll result-index convention

This note records the decision between the two `roll` conventions and the
consequences for the transport metatheory.  It is a design record; it is not a
proof.

## The two expressions

`Core.HasType.roll` (`Transport/Mltt/Core.lean:340`) concludes at

```text
.ind I (args.take sig.params.length
        ++ ctor.indices.map (substParams (args.take sig.params.length)))
```

so constructor result indices are substituted by **data parameters only**.

`HasTypeDep.rollDep` (`Transport/Mltt/Dependent.lean:55`) concludes at

```text
.ind I (args.take sig.params.length
        ++ ctor.indices.map (substMany args))
```

so constructor result indices are substituted by the **full argument list**,
matching `WellFormedSigFull`.

## Decision

Keep `Core.HasType.roll` unchanged.

Reasons:

- The `Eq`/`J` development and `hasType_weaken_proof` are built on the old
  parameter-only convention and use the Eq-specific index lemmas
  (`indTyList`, `rollIndexArgs`, `paramsTyList_rename`, `indicesTyList_rename`).
- Changing `HasType.roll` makes `Eq_sig` denote a different type: for
  `args = [A, x]`, the old result index is `x`, the full-argument one is `A`.
- The full-argument convention is already represented by `EqDep_sig` and
  `HasTypeDep.rollDep`; migrating Eq is a separate change.

`HasTypeDep` therefore embeds the old `HasType` derivation and carries both
conventions.  Nothing currently asserts they agree, so no theorem is
contradictory; the union is intentional and transitional.

## Consequence for weakening

A `HasTypeDep` weakening proof must handle `ofHasType`, so it needs the general
old-judgment renaming:

```text
WellFormedEnv env ->
Wk ρ Γ Δ ->
HasType env Γ t A ->
HasType env Δ (Tm.rename ρ t) (Tm.rename ρ A)
```

with `Wk` from `Transport/Mltt/Weaken.lean:400` and `WellFormedEnv` from
`Transport/Mltt/Scoped.lean:161`.  The existing `hasType_weaken` is only the
`[Eq_sig]` instance.

The general full-argument signature lemmas (`rollIndexArgsFull_rename`,
`sigTyListFull_rename`, `rollIndexArgsFull_subst`, `sigTyListFull_subst`) serve
the `HasTypeDep.rollDep` side; they are not a replacement for the old Eq
lemmas.

## Deferred

- Migrating `Eq_sig` to `EqDep_sig` and rewriting `J`/context/weakening.
- Unifying `HasType` and `HasTypeDep` into one full-argument judgment.
- Case-motive context insertion/weakening (separate note in
  `docs/mltt-programme.md`).
