# Gallai–van der Waerden numbers from `m`-th power residue colourings

A Lean 4 proof, with Mathlib, of two lower-bound constructions for the Gallai–van der Waerden numbers
`GW(r; k, l)` of Mao, Ozeki, Robertson and Wang, for rainbow `(m + 1)`-term progressions and every
`m`. It is laid out for registration on [Palomar](https://palomar-registry.org): `Challenge.lean`
states the results, `Solution.lean` proves them, and `comparator.json` names the compared theorems.
Submissions go through the form at https://submit.palomar-registry.org/.

## The results

Write `[1, n] = {1, …, n}`. An exact `r`-colouring of `[1, n]` uses all `r` colours. A `k`-term
arithmetic progression (AP) is rainbow when its `k` terms have pairwise distinct colours; an `l`-term
AP is monochromatic when its terms all have one colour; common differences are at least 1. Following
Mao, Ozeki, Robertson and Wang (MORW; J. Combin. Theory Ser. A 193 (2023) 105672, Definition 1.15),
`GW(r; k, l)` is the least `M` such that for every `n ≥ M`, every exact `r`-colouring of `[1, n]`
contains a rainbow `k`-term AP or a monochromatic `l`-term AP.

Let `p` be a prime with `p ≡ 1 (mod m)`. The `m`-th power class of a residue `a` is
`a^((p - 1)/m) mod p`; the nonzero residues fall into exactly `m` classes (the `m`-th roots of unity
modulo `p`), and the class of `0` is `0`. The two conditions:

- (i) for every `i ∈ {0, …, m}`, the `m` residues `j - i` (`j ∈ {0, …, m}`, `j ≠ i`) do not lie in
  `m` distinct classes;
- (ii) no `l` consecutive integers in `[1, p - 1]` lie in one class.

**Theorem 4.** Let `l ≥ 2` and let `p > l` be a prime with `p ≡ 1 (mod m)` satisfying (i) and (ii).
Colour `x ∈ [1, (l - 1)p]` by `(x - 1)^((p - 1)/m) mod p`: the class of `x - 1` when `x ≢ 1 (mod p)`,
and the new colour `0` on the zero class `x ≡ 1 (mod p)`. This colouring uses exactly `m + 1`
colours and has no rainbow `(m + 1)`-term AP and no monochromatic `l`-term AP. Hence
`GW(m + 1; m + 1, l) > (l - 1)p`.

**Theorem 8.** With `m, l, p` as in Theorem 4, let `s ≥ 2` and let `z` colour `{0, …, l - 1}` with
exactly `s` colours and no rainbow `(m + 1)`-term AP. Colour `x ∈ [1, (l - 1)p + 1]` by the class of
`x - 1` when `x ≢ 1 (mod p)`, and the point `x = 1 + kp` by the new colour `z(k)`. This colouring uses
exactly `m + s` colours and has no rainbow `(m + 1)`-term AP and no monochromatic `l`-term AP. Hence
`GW(m + s; m + 1, l) > (l - 1)p + 1`.

The theorem numbers are those of Quantavane's internal note on these numbers, which states
Theorem 4 for `m ≥ 2`, `l ≥ 4` and Theorem 8 for `m ≥ 2`, `l ≥ 3`. Here `p ≡ 1 (mod m)` with `p` prime
already forces `m ≥ 2`, and the proofs need only `l ≥ 2`, so the Lean statements assume `l ≥ 2` and
contain the note's cases. For `m = 2`, condition (i) says `(2 | p) = (-1 | p) = 1`, that is
`p ≡ 1 (mod 8)`, and Theorem 8 is then the quadratic-residue construction of
[quantavane-gw-residue](https://github.com/arhancanli/quantavane-gw-residue) (its Theorem 1).

Instances, all with `l = 4`: `(m, p) = (3, 109)`, `(4, 353)` and `(5, 751)` satisfy (i) and (ii), so

- Theorem 4 gives `GW(4; 4, 4) > 327`, `GW(5; 5, 4) > 1059` and `GW(6; 6, 4) > 2253`;
- Theorem 8 gives `GW(6; 4, 4) > 328` (`m = 3`, `p = 109`, `z = 0, 1, 2, 0`) and
  `GW(8; 5, 4) > 1060` (`m = 4`, `p = 353`, `z = 0, 1, 2, 3`).

## What is compared (`comparator.json`)

All thirteen theorems are stated in `Challenge.lean` (with `sorry`) and proved in `Solution.lean`.

| Lean name | What it says |
|---|---|
| `GwPower.theorem4` | Theorem 4: for `c = powerColour p m` and `N = (l - 1)p`, (a) `c` takes exactly `m + 1` values on `[1, N]`, (b) no `(m + 1)`-term AP in `[1, N]` is rainbow, (c) no `l`-term AP in `[1, N]` is monochromatic. |
| `GwPower.exists_goodExactColouring` | Under the same hypotheses, `[1, (l - 1)p]` has a good exact `(m + 1)`-colouring (colours `Fin (m + 1)`) for `(m + 1, l)`. |
| `GwPower.lt_of_gwProperty` | Every `M` with the defining property of `GW(m + 1; m + 1, l)` is greater than `(l - 1)p`. |
| `GwPower.lt_GW` | The same inequality for the number `GW (m + 1) (m + 1) l`, assuming some `M` has the property. |
| `GwPower.theorem8` | Theorem 8: for `c = splitColour p m s z` and `N = (l - 1)p + 1`, (a) `c` takes exactly `m + s` values on `[1, N]`, (b) no `(m + 1)`-term AP in `[1, N]` is rainbow, (c) no `l`-term AP in `[1, N]` is monochromatic. |
| `GwPower.exists_goodExactColouring_split` | Under the same hypotheses, `[1, (l - 1)p + 1]` has a good exact `(m + s)`-colouring for `(m + 1, l)`. |
| `GwPower.lt_of_gwProperty_split` | Every `M` with the defining property of `GW(m + s; m + 1, l)` is greater than `(l - 1)p + 1`. |
| `GwPower.lt_GW_split` | The same for the number `GW (m + s) (m + 1) l`, assuming some `M` has the property. |
| `GwPower.gw_4_4_4` | Every `M` with the defining property of `GW(4; 4, 4)` is greater than 327. |
| `GwPower.gw_5_5_4` | Every `M` with the defining property of `GW(5; 5, 4)` is greater than 1059. |
| `GwPower.gw_6_6_4` | Every `M` with the defining property of `GW(6; 6, 4)` is greater than 2253. |
| `GwPower.gw_6_4_4` | Every `M` with the defining property of `GW(6; 4, 4)` is greater than 328. |
| `GwPower.gw_8_5_4` | Every `M` with the defining property of `GW(8; 5, 4)` is greater than 1060. |

`definition_names` is empty on purpose. The seven definitions the statements use (below) are spelled
out in full in `Challenge.lean`; Comparator follows them from the theorem statements and requires
them to be identical in the Solution, which takes them from `GwPower/Defs.lean`.

## Definitions, and how they match the paper

- `IsGoodExactColouring r k l n c`: every colour `col : Fin r` occurs on `[1, n]`; no
  `x, x + d, …, x + (k - 1)d` in `[1, n]` with `d ≥ 1` has pairwise distinct colours; no
  `x, x + d, …, x + (l - 1)d` in `[1, n]` with `d ≥ 1` is monochromatic. The colouring
  `c : ℕ → Fin r` is defined on all of `ℕ`; only its values on `[1, n]` matter.
- `GWProperty r k l M`: for every `n ≥ M` and every `c`, `¬ IsGoodExactColouring r k l n c`. This is
  the defining property in MORW Definition 1.15 (for every `n ≥ M`, not only `n = M`, since
  exactness does not pass to sub-intervals).
- `GW r k l := sInf {M | GWProperty r k l M}`. In Lean the infimum of the empty set of natural numbers
  is `0`. The Gallai–van der Waerden theorem (that some `M` has the property) is not formalised here,
  so `lt_GW` and `lt_GW_split` assume it (`hex`). The threshold forms and the instances need no such
  assumption.
- `ConditionI m p` and `ConditionII m l p`: conditions (i) and (ii), with the class of `a` written as
  `a ^ ((p - 1) / m)` in `ZMod p`. (i) is encoded as: for every `i ≤ m` there are `j₁ ≠ j₂`, both
  `≤ m` and `≠ i`, whose residues `j₁ - i`, `j₂ - i` have the same class; that is, the `m` residues
  `j - i` are not in `m` distinct classes.
- `powerColour p m x := ((x : ZMod p) - 1) ^ ((p - 1) / m)`: the colouring of Theorem 4, with colours
  in `ZMod p`. On the zero class it is `0`, which is not an `m`-th root of unity, so it is the new
  colour. "Exactly `m + 1` colours" is stated as `((Finset.Icc 1 N).image c).card = m + 1`.
- `splitColour p m s z x`: the colouring of Theorem 8, with colours `ZMod p ⊕ Fin s`:
  `Sum.inr (z ((x - 1) / p))` if `x % p = 1`, else `Sum.inl ((x - 1) ^ ((p - 1) / m))`. The colouring
  `z : ℕ → Fin s` of the zero class is a function on `ℕ` whose values at `0, …, l - 1` matter:
  `hz` says it takes every value there, `hzk` that it has no rainbow `(m + 1)`-term AP there.
- The GW corollaries need colours `Fin r`; `exists_good_of_card` in `GwPower/Basic.lean` relabels the
  `m + 1` (or `m + s`) values taken on `[1, N]` as `Fin (m + 1)` (or `Fin (m + s)`).

## How the proof goes (`GwPower/Basic.lean`)

- `exp_mul`, `exp_pos`: `p % m = 1` gives `m ∣ p - 1`, so `((p - 1)/m) · m = p - 1` and the exponent
  `(p - 1)/m` is positive; by Fermat, the class of a nonzero residue is an `m`-th root of unity.
- `card_classes`: the nonzero residues have exactly `m` classes. At most `m`, since `X^m = 1` has at
  most `m` roots in the field `ZMod p` (Mathlib's `Polynomial.card_nthRoots`); at least `m`, since each
  class contains at most `(p - 1)/m` residues (roots of `X^((p - 1)/m) = b`) and there are `p - 1`
  nonzero residues (`Finset.card_le_mul_card_image`).
- `card_image` (Theorem 4 (a)): the values on `[1, (l - 1)p]` are `0` and the `m` classes;
  `split_card_image` (Theorem 8 (a)): the `m` classes (`Sum.inl`) and the `s` colours of `z`
  (`Sum.inr`), using `hz`.
- `no_rainbow` (Theorem 4 (b), for every `x`, `d`): if a term `x + id` lies in the zero class, then the
  other terms have residues `(j - i)d`, of classes `cls(j - i) cls(d)`, and (i) makes two of them
  equal. Otherwise all `m + 1` colours are `m`-th roots of unity, and there are at most `m` of them
  (pigeonhole, `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`).
- `no_mono` (Theorem 4 (c)): an `l`-term AP in `[1, (l - 1)p]` has `p ∤ d`. With `x - 1 ≡ Ad (mod p)`
  the term `x + jd` has colour `((A + j)d)^((p - 1)/m)`. If some `A + i ≡ 0`, that term has colour `0`
  and any other term a nonzero colour (`|j - i| < l < p`). Otherwise `A ≡ a` with `a, …, a + l - 1`
  in `[1, p - 1]`, and cancelling the class of `d` turns a monochromatic AP into `l` consecutive
  integers in one class, against (ii).
- `split_no_rainbow` (Theorem 8 (b)): two terms in the zero class force `p ∣ d`, so the AP lies in the
  zero class with indices `k, k + e, …, k + me`, and `hzk` applies. With at most one term in the zero
  class, a rainbow AP for `splitColour` would be rainbow for `powerColour`, against `no_rainbow`.
- `split_no_mono` (Theorem 8 (c)): if `p ∣ d` then `d = p`, `x = 1` and the AP is the whole zero class,
  coloured by `z`, which is not constant (`hz`, `s ≥ 2`). If `p ∤ d`, no term lies in the zero class
  and the `powerColour` values are constant, against `no_mono_core`.
- The instances: `conditionI_of_nat` and `conditionII_of_nat` restate (i) and (ii) with
  natural-number arithmetic (`a ^ ((p - 1)/m) % p`), which `decide` checks by kernel evaluation
  (`decide +kernel` for `p = 353` and `p = 751`; no `native_decide`). The colourings `z = 0, 1, 2, 0`
  and `z = 0, 1, 2, 3` are checked onto and rainbow-free by `decide` and `omega`.

No `sorry` outside `Challenge.lean`, no `native_decide`, no extra axioms:
`lake env lean scripts/CheckAxioms.lean` prints `[propext, Classical.choice, Quot.sound]` for each
compared theorem.

## Why it is of interest

Gallai–van der Waerden numbers were introduced by Mao, Ozeki, Robertson and Wang (2023) as the
arithmetic analogue of Gallai–Ramsey numbers; published exact values exist only for `l = 3`. Theorems
4 and 8 turn power-residue colourings, Rabung's classical lower-bound method for van der Waerden
numbers, into explicit lower bounds for rainbow `(m + 1)`-term progressions for every `m`: the new
colour on the zero class `1, 1 + p, 1 + 2p, …` is what makes them exact colourings, and condition (i)
is exactly what keeps every progression through the zero class from being rainbow. The instances
give, for example, `GW(5; 5, 4) > 1059` and `GW(6; 6, 4) > 2253`; primes found by a computer search
(not formalised here) give more, for example `GW(r; 5, 5) ≥ 19,750` for `r = 6, 7, 8` with `m = 4`,
`p = 4937`. The natural readers are researchers in Ramsey theory on the integers and arithmetic
combinatorics: van der Waerden numbers, rainbow (anti-van der Waerden) problems and Gallai–Ramsey
colourings.

## Provenance, literature and novelty

The constructions and Theorems 4 and 8 were found on 11 and 12 November 2026 in Quantavane's research
work and are first presented here (an internal note of Quantavane has the same statements and
proofs). The residue part of the colouring is the classical power-residue idea for van der Waerden
lower bounds (Rabung, Canad. Math. Bull. 22 (1979) 87–91; Rabung and Lotts, Electron. J. Combin.
19(2) (2012) #P35). What is new here is the Gallai setting: the zero class receives its own colour or
colouring, and condition (i) keeps every progression through it from being rainbow.

Literature search (11 November 2026, recorded in Quantavane's note): MORW give definitions, values for
`l = 3` and asymptotic bounds; Y. Si (arXiv:2610.30711, October 2026) determines `GW(r; 3, 3)` for
every `r`; two web searches found no published value of a Gallai–van der Waerden number with
`l ≥ 4`. We know of no earlier construction of this kind and no published value or bound of the
numbers in the instances. The search was limited, so novelty is our reading, not an established
fact.

## Authorship and the role of AI

Author and maintainer: Arhan Canli (Quantavane), who takes responsibility for the result.

The constructions, their informal proofs and the Lean proof were produced by AI agents (Claude, by
Anthropic) working for Quantavane under Arhan Canli's direction: Quantavane's coordinating agent found
Theorem 4 and wrote its informal proof; two further agents found Theorem 6 (the cubic case of
Theorem 8) and Theorem 8 and wrote their informal proofs; another agent wrote this Lean proof
(Lean v4.35.0) and ran the checks listed in `NOTES.md`. No mathematician outside Quantavane has
reviewed the proof.

## Checking it

Lean `v4.35.0` (`lean-toolchain`) and Mathlib `v4.35.0`
(`56a005855ea17e0b0958f73ec801ae140b0a1679`, pinned in `lake-manifest.json`).

```sh
lake exe cache get        # prebuilt Mathlib
lake build                # GwPower, Challenge, Solution
lake env lean scripts/CheckAxioms.lean
lake comparator           # Linux with bubblewrap: compares Challenge and Solution and replays the proofs
```

`.github/workflows/palomar-preflight.yml` runs Palomar's own mechanical check
(`PalomarRegistry/PalomarSubmission`, pinned commit) on every push to `main`.

## Files

- `Challenge.lean`: the statement of record (Mathlib imports only, about 230 lines).
- `Solution.lean`: the thirteen compared theorems with proofs.
- `GwPower/Defs.lean`: the seven definitions, identical to those in `Challenge.lean`.
- `GwPower/Basic.lean`: the proof.
- `comparator.json`, `formalization.yaml`, `scripts/CheckAxioms.lean`, `NOTES.md` (local checks).

## Licence

Apache-2.0 (`LICENSE`).
