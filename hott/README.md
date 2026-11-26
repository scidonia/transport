# Lean HoTT route

This package reuses [Ground Zero](https://github.com/rzrn/ground_zero), a Lean 4
HoTT library, for the univalent layer.  Ground Zero is vendored at commit
`2cbca29485c2e6f420c120365e00fe3b70db3acf` (Apache-2.0) under
`vendor/ground_zero`.

- Toolchain: Lean 4.27.0 (`lean-toolchain` here and in the vendored package).
- `Hott/Univalence.lean` uses `ua (ideqv A)` and `uaβ` over Ground Zero's
  proof-relevant `Id`/`Path` type.  `notTransport` is the nontrivial
  computation: transport along `ua notEquiv` sends `true` to `false`.
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

## Consistency

Univalence over a proof-relevant identity type is an axiom of HoTT and is
consistent relative to cubical sets and groupoids.  Ground Zero takes
`uaweak` as an axiom and uses a large-eliminator checker; it does not
formalise the consistency model.  Kubus does, with a verified kernel, a
cubical-sets model, and canonicity.

The inconsistency in `Transport/UnivalenceObstruction.lean` is specific to
Lean's proof-irrelevant `Eq` plus the full round-trip law.  It is not a
statement against HoTT or against Ground Zero's `Id`.

## Related Lean 4 formalisations

| project | what it is | fit here |
| --- | --- | --- |
| [`rzrn/ground_zero`](https://github.com/rzrn/ground_zero) | synthetic HoTT library: proof-relevant `Id`/`Path`, `ua`/`uaβ`, HITs via quotients, custom large-eliminator checker; Apache-2.0 | vendored here; Lean 4.27 |
| [`sinhp/HoTTLean`](https://github.com/sinhp/HoTTLean) | groupoid model of HoTT and SynthLean proof mode; depends on Mathlib and Poly; Lean 4.25.0-rc2 | not a drop-in univalence library; heavier toolchain |
| [`mitschabaude-bot/kubus`](https://github.com/mitschabaude-bot/kubus) | verified kernel for CCHM cubical type theory, univalence and canonicity in its object language; Lean 4.30 | separate proof assistant and `.ktt` language, not an importable Lean library |
| [`theckl/cHoTT4`](https://github.com/theckl/cHoTT4) | Lean 4 model of cubical type theory (2024) | model development, not a maintained library |
| [`merzougao/HoTT_Lean4`](https://github.com/merzougao/HoTT_Lean4) | early 2023 HoTT-in-Lean 4 start | not viable as a dependency |

Ground Zero is the practical Lean 4 library with `ua`/`uaβ`; Kubus is the most
thoroughly verified univalent *object theory*, but it is a separate proof
assistant rather than a Lean import.
