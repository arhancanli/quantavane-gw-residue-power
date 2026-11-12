# Notes: what is proved and how it was checked (12 November 2026)

## What is proved

Everything below is proved in Lean 4 (v4.35.0, Mathlib v4.35.0) with no `sorry`, no `native_decide`
and only the axioms `propext`, `Classical.choice` and `Quot.sound`. The statements of record are in
`Challenge.lean`; `comparator.json` names the thirteen compared theorems.

- **Theorem 4 in full generality** (`GwPower.theorem4`): for every `m`, every `l ≥ 2` and every prime
  `p > l` with `p % m = 1` satisfying conditions (i) (`ConditionI m p`) and (ii)
  (`ConditionII m l p`), the colouring `powerColour p m x = (x - 1) ^ ((p - 1) / m)` in `ZMod p`
  takes exactly `m + 1` values on `[1, (l - 1)p]` and has no rainbow `(m + 1)`-term AP and no
  monochromatic `l`-term AP there. Corollaries: a good exact `(m + 1)`-colouring with colours
  `Fin (m + 1)` exists (`exists_goodExactColouring`), every threshold `M` of `GW(m + 1; m + 1, l)`
  exceeds `(l - 1)p` (`lt_of_gwProperty`), and so does `GW (m + 1) (m + 1) l` if a threshold exists
  (`lt_GW`).
- **Theorem 8 in full generality** (`GwPower.theorem8`), the `m`-th power form of the note's
  Theorem 6: with `m, l, p` as above, `s ≥ 2` and `z : ℕ → Fin s` taking all `s` values on
  `{0, …, l - 1}` with no rainbow `(m + 1)`-term AP there, the colouring `splitColour p m s z`
  (classes on `x ≢ 1 (mod p)`, `z ((x - 1)/p)` on the zero class) takes exactly `m + s` values on
  `[1, (l - 1)p + 1]` and has no rainbow `(m + 1)`-term AP and no monochromatic `l`-term AP there.
  Corollaries as for Theorem 4: `exists_goodExactColouring_split`, `lt_of_gwProperty_split`
  (`GW(m + s; m + 1, l) > (l - 1)p + 1`), `lt_GW_split`.
- **Instances** (threshold form, `l = 4`): `gw_4_4_4` (`GW(4; 4, 4) > 327`, `m = 3`, `p = 109`),
  `gw_5_5_4` (`GW(5; 5, 4) > 1059`, `m = 4`, `p = 353`), `gw_6_6_4` (`GW(6; 6, 4) > 2253`, `m = 5`,
  `p = 751`), `gw_6_4_4` (`GW(6; 4, 4) > 328`, Theorem 8 with `m = 3`, `p = 109`, `z = 0, 1, 2, 0`) and
  `gw_8_5_4` (`GW(8; 5, 4) > 1060`, Theorem 8 with `m = 4`, `p = 353`, `z = 0, 1, 2, 3`). Conditions (i)
  and (ii) are checked by `decide` on natural-number arithmetic (`decide +kernel` for `p = 353`,
  `751`).

Relation to the note: the note states Theorem 4 for `m ≥ 2`, `l ≥ 4` and Theorem 8 for `m ≥ 2`,
`l ≥ 3`. The Lean statements have no hypothesis on `m` (`p % m = 1` with `p` prime forces `m ≥ 2`) and
assume only `l ≥ 2`, so they contain the note's statements. Theorem 2 (cubic residues) is the case
`m = 3` of Theorem 4, and Theorem 6 the case `m = 3` of Theorem 8, with condition (i) in the general
form; the note's cubic form of (i) (`v(2) = 1` or `v(3) = 1` or `v(2) = v(3)`) is equivalent because
`-1` is a cube, but that equivalence is not formalised.

## Line counts

| File | Lines |
|---|---|
| `Challenge.lean` | 227 (13,663 bytes) |
| `Solution.lean` | 105 |
| `GwPower/Defs.lean` | 67 |
| `GwPower/Basic.lean` | 607 |
| `GwPower.lean` | 4 |
| `scripts/CheckAxioms.lean` | 25 |

Every `.lean` file starts with `module`; `Challenge.lean` imports only Mathlib
(`Mathlib.Data.ZMod.Basic`, `Mathlib.Order.Interval.Finset.Nat`, `Mathlib.Order.Lattice.Nat`).

## Checks run (Mac, Apple silicon, Lean v4.35.0)

All on a fresh clone of commit `50648106bb975d1e0d92c844fa2f20f0a11a9696` (the commit before this
file was added; no Lean file changed since), with the Lake packages of the pinned Mathlib checkout
and the project's own modules built from scratch.

1. `lake build`:

   ```
   ✔ [2012/2019] Built GwPower.Defs (3.4s)
   ⚠ [2013/2019] Built Challenge (3.0s)      (13 warnings: declaration uses `sorry`, as intended)
   ✔ [2015/2019] Built GwPower.Basic (4.1s)
   ✔ [2016/2019] Built GwPower (1.3s)
   ✔ [2018/2019] Built Solution (1.3s)
   Build completed successfully (2019 jobs).
   ```

2. `lake env lean scripts/CheckAxioms.lean`: each of the thirteen compared theorems
   (`theorem4`, `exists_goodExactColouring`, `lt_of_gwProperty`, `lt_GW`, `theorem8`,
   `exists_goodExactColouring_split`, `lt_of_gwProperty_split`, `lt_GW_split`, `gw_4_4_4`,
   `gw_5_5_4`, `gw_6_6_4`, `gw_6_4_4`, `gw_8_5_4`) prints

   ```
   'GwPower.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. `lake comparator` (with the toolchain's `bin` directory, which holds `nanoda_bin`, on `PATH`):

   ```
   error: `lake comparator` sandboxes the code it checks with `bwrap`, which needs Linux namespaces.
   exit 2
   ```

   Lake's comparator needs bubblewrap, which does not exist on macOS, so it could not run here in
   its normal mode. The `--inadvisably-no-sandbox` mode was not used. Palomar's preflight workflow
   (`.github/workflows/palomar-preflight.yml`) runs the comparator on Linux after a push. In its
   place, the steps the comparator performs were run by hand (4 and 5).

4. Statement comparison. A script collected, in the Challenge and in the Solution environment, every
   constant reachable from the types of the thirteen compared theorems (following definition values,
   not proofs) and printed each type and value with `pp.all` and hashes. The two outputs (13 roots,
   835 constants) are identical except for the module that holds the seven own definitions
   (`Challenge` versus `GwPower.Defs`).

5. Kernel replays. `leanexport` (the comparator's exporter) wrote both modules with the compared
   theorems as targets; the Solution export was replayed through every kernel bundled with the
   toolchain:

   ```
   leanchecker            rc 0
   nanoda                 rc 0
   con-ron                rc 0   accepted 11945 declarations (--verified)
   leanchecker-paranoid   rc 0
   lean4lean              rc 0   checked 11942 declarations
   con-leche              rc 0   accepted 11945 declarations (--verified)
   ```

   NanoDa with unpermitted axioms as a hard error: Solution export exit 0; Challenge export exit 1
   (`export file declares unpermitted axiom "sorryAx"`), as it should. `Lean.ofReduceBool` does not
   occur in the Solution export. SHA-256 of the exports: `solution.ndjson`
   `1c93903b46e98bcbbb3d6c3651bf68a6de102d4d092be2a5993872e519ab7f85`, `challenge.ndjson`
   `3aa34f13f6219aff801e678d18fbb55e684d4e7b689612c0fff74709b1e21a09`.

6. The instance colourings were also checked numerically before the Lean work (a separate brute-force
   program): exactly `m + 1` (or `m + s`) colours, no rainbow `(m + 1)`-term AP and no monochromatic
   4-term AP for `p = 109`, `353` (Theorem 4) and for the two Theorem 8 colourings.

## What remains

- Palomar's mechanical preflight (the workflow above, on GitHub's Linux runners) has not run: it needs
  the repository to be public on GitHub. Until then the comparator itself has not run on this code
  (steps 4 and 5 replace it locally).
- No review outside the agent that wrote the Lean proof; `formalization.yaml` says
  `self-assessed`.
- Not formalised: the Gallai–van der Waerden theorem (that a threshold exists; `lt_GW` and
  `lt_GW_split` assume it); which primes satisfy (i) and (ii) in general (the note uses Weil's bound
  and a computer search); exact values of any GW number; the equivalence of the cubic form of (i)
  with `ConditionI 3 p`.
