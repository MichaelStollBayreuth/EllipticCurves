# Comparator verification harness

This directory lets [Comparator](https://github.com/leanprover/comparator) — "a trustworthy judge
for Lean proofs" — certify that this repository proves its two headline results, independently of
the repository's own build and using only the permitted axioms:

* the **Mordell-Weil Theorem** over a number field
  (`WeierstrassCurve.Affine.fg_point_of_numberField`);
* the **show-piece example** `E(ℚ) ≅ ℤ` for `E : y² = x³ - x + 1`
  (`InfiniteOrderExample.nonempty_point_addEquiv_int`).

## What is checked

- [`Challenge.lean`](Challenge.lean) imports **only Mathlib** and states both results with `sorry`
  proofs. Every notion in the statements (`WeierstrassCurve.Affine`, its group of points `Point`,
  `WeierstrassCurve.IsElliptic`, `NumberField`, `AddGroup.FG`, `≃+`) is a Mathlib definition, so it
  reproduces nothing from this repository and is a self-contained specification of the claims; the
  example curve and its `IsElliptic` instance are defined in the challenge itself, from Mathlib
  notions only.
- [`Solution.lean`](Solution.lean) imports `EllipticCurves.MordellWeil` and
  `EllipticCurves.RankExample` and proves those statements via the library theorems.

Comparator builds both modules (the solution in a sandbox), exports them with `lean4export`, and
checks that each challenge theorem in the solution:

1. proves the **same statement** as in the challenge — comparing the full bodies (not just the
   types) of every definition the statement transitively refers to (here, all from Mathlib);
2. uses no axioms beyond `permitted_axioms` (`propext`, `Quot.sound`, `Classical.choice`);
3. is accepted by the Lean kernel.

Because the statements are expressed entirely in Mathlib terms, nothing from the library is
reproduced in the challenge; the challenge and solution statements are literally identical.

## Config

[`challenges.json`](challenges.json) — theorems `challenge_fg_point_of_numberField` and
`challenge_nonempty_point_addEquiv_int`.

## Running

Prerequisites (see the Comparator README): a built `comparator` binary, `landrun` built from its
`main` branch, and — crucially — a `lean4export` built at **the same Lean version as this project**
(it loads the project's `.olean`s), i.e. the tag matching `lean-toolchain`. Point Comparator at them
via `COMPARATOR_LANDRUN` / `COMPARATOR_LEAN4EXPORT`, or put them on `PATH`.

Once installed, the wrapper [`scripts/run-comparator.sh`](../scripts/run-comparator.sh) builds the
library and runs the check (override binary locations with `COMPARATOR_BIN` /
`COMPARATOR_LEAN4EXPORT` / `COMPARATOR_LANDRUN`):

```bash
scripts/run-comparator.sh
```

The manual equivalent, run from the **repository root** (Comparator uses the current directory as
the project and invokes `lake build Challenge` / `lake build Solution` there):

```bash
lake exe cache get                       # trusted Mathlib oleans, optional
lake build EllipticCurves                # so the Solution build reuses the library oleans
lake env /path/to/comparator comparator/challenges.json
```

Exit code `0` (and `Your solution is okay!`) means the check passed.

The `Challenge`/`Solution` libraries are declared in the root `lakefile.toml` but are excluded from
`defaultTargets`, so a plain `lake build` does not build them and the deliberate `sorry` in
`Challenge.lean` never enters the library build.
