# Comparator verification harness

This directory lets [Comparator](https://github.com/leanprover/comparator) — "a trustworthy judge
for Lean proofs", built into Lake as `lake comparator` since Lean v4.35.0 — certify that this repository proves its two headline results, independently of
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

`lake comparator` builds and exports both modules inside a `bubblewrap` sandbox (it never loads
the project's `.olean`s into its own process) and checks that each challenge theorem in the
solution:

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

Run from the **repository root**; the only prerequisite besides Lean is `bubblewrap` (`bwrap`)
with unprivileged user namespaces (or installed setuid root):

```bash
scripts/run-comparator.sh               # = lake build EllipticCurves && lake comparator --config comparator/challenges.json
scripts/run-comparator.sh --paranoid    # also run all external checkers bundled with Lean
```

Exit code `0` (and `Your solution is okay!`) means the check passed, `1` that it was rejected, `2`
that it could not start (no `bwrap`, no `lake-manifest.json`, a malformed configuration). The
wrapper builds the library first: the sandbox cannot write to the project directory, and with a
current build the sandboxed builds only replay it (about five minutes in all, most of it the
export).

Until 2026-10-15 the check ran on the external tools — a separately built `comparator` binary,
`landrun`, and a `lean4export` built at the project's Lean version — through an earlier version of
the wrapper (see the history of `scripts/run-comparator.sh`); `lake comparator` replaces all three.

The `Challenge`/`Solution` libraries are declared in the root `lakefile.toml` but are excluded from
`defaultTargets`, so a plain `lake build` does not build them and the deliberate `sorry` in
`Challenge.lean` never enters the library build.
