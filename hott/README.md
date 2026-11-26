# Lean HoTT route

This package reuses [Ground Zero](https://github.com/rzrn/ground_zero), a Lean 4
HoTT library, for the univalent layer.  Ground Zero is vendored at commit
`2cbca29485c2e6f420c120365e00fe3b70db3acf` (Apache-2.0) under
`vendor/ground_zero`.

- Toolchain: Lean 4.27.0 (`lean-toolchain` here and in the vendored package).
- `Hott/Univalence.lean` uses `ua (ideqv A)` and `uaβ` over Ground Zero's
  proof-relevant `Id`/`Path` type.
- The `[GroundZero]` marker instance is supplied explicitly; Ground Zero's
  `uaweak` remains an axiom, as in the upstream library.

Why 4.27 and not the main 4.35 project: Lean 4.35's `Transitive`/`Reflexive`
classes are `Prop`-valued, while Ground Zero's `Id` is `Type`-valued.  The
vendored library builds as written on 4.27; the main 4.35 core cannot compile
it unmodified.

```bash
# with Lean 4.27.0 on PATH
lake build
```
