module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Gallai–van der Waerden numbers from `m`-th power residue colourings: the statement

This file is the statement of record. It imports only Mathlib, defines the notions the statements
use, and states the results with `sorry`. `Solution.lean` proves every statement; `comparator.json`
names the compared theorems. The definitions below must agree exactly with the ones the proof uses
(Comparator checks this), so they are spelled out here in full.

## Gallai–van der Waerden numbers

Write `[1, n] = {1, …, n}`. An *exact `r`-colouring* of `[1, n]` is a colouring of `[1, n]` with
`r` colours in which every colour occurs. An arithmetic progression (AP) always has common
difference `d ≥ 1`. A `k`-term AP `x, x + d, …, x + (k - 1)d` is *rainbow* when its `k` terms have
pairwise distinct colours, and an `l`-term AP is *monochromatic* when all its terms have the same
colour. The Gallai–van der Waerden number `GW(r; k, l)` of Mao, Ozeki, Robertson and Wang
(J. Combin. Theory Ser. A, 2023, Definition 1.15) is the least `M` such that, for every `n ≥ M`,
every exact `r`-colouring of `[1, n]` contains a rainbow `k`-term AP or a monochromatic `l`-term AP.

## Power residue classes

Let `p` be a prime with `p ≡ 1 (mod m)`. The `m`-th power class of a residue `a` modulo `p` is the
value `a ^ ((p - 1) / m)` in `ZMod p`. For `a ≢ 0` it is an `m`-th root of unity, there are exactly
`m` such values, and two nonzero residues have the same value exactly when their quotient is an
`m`-th power. The class of `0` is `0`. Two conditions on `(m, l, p)` (`ConditionI`, `ConditionII`):

* (i) for every `i ∈ {0, …, m}`, the `m` residues `j - i` (`j ∈ {0, …, m}`, `j ≠ i`) do not lie in
  `m` distinct classes;
* (ii) no `l` consecutive integers `a, a + 1, …, a + l - 1` in `[1, p - 1]` lie in one class.

## Theorem 4 (rainbow `(m + 1)`-term APs)

Let `l ≥ 2` and let `p > l` be a prime with `p ≡ 1 (mod m)` satisfying (i) and (ii). Put
`N = (l - 1)p` and colour `x ∈ [1, N]` by `(x - 1) ^ ((p - 1) / m)` in `ZMod p` (`powerColour`): the
class of `x - 1` when `x ≢ 1 (mod p)`, and the new colour `0` on the zero class `x ≡ 1 (mod p)`.
Then (a) exactly `m + 1` colours occur on `[1, N]`, (b) no `(m + 1)`-term AP in `[1, N]` is
rainbow, and (c) no `l`-term AP in `[1, N]` is monochromatic. Hence `GW(m + 1; m + 1, l) > (l - 1)p`.

## Theorem 8 (the zero class split by a colouring `z`)

With `m, l, p` as in Theorem 4, let `s ≥ 2` and let `z` colour `{0, …, l - 1}` with all `s` colours
`Fin s` and no rainbow `(m + 1)`-term AP. Put `N = (l - 1)p + 1` and colour `x ∈ [1, N]` by
`Sum.inl` of the class of `x - 1` when `x ≢ 1 (mod p)` and by the new colour `Sum.inr (z k)` when
`x = 1 + kp` (`splitColour`). Then (a) exactly `m + s` colours occur on `[1, N]`, (b) no
`(m + 1)`-term AP in `[1, N]` is rainbow, and (c) no `l`-term AP in `[1, N]` is monochromatic.
Hence `GW(m + s; m + 1, l) > (l - 1)p + 1`.

The hypotheses are stated as Quantavane's note states them, except that the note assumes `m ≥ 2`
and `l ≥ 4` (Theorem 4) or `l ≥ 3` (Theorem 8). Here `p % m = 1` already forces `m ≥ 2` (since
`p % 0 = p` and `p % 1 = 0`), and the proofs need only `l ≥ 2`, so the theorems below are stated with
`2 ≤ l`; they include the note's cases.

## Instances

The hypotheses can be met. With `l = 4`: `(m, p) = (3, 109)`, `(4, 353)` and `(5, 751)` satisfy (i)
and (ii); Theorem 4 gives `GW(4; 4, 4) > 327`, `GW(5; 5, 4) > 1059` and `GW(6; 6, 4) > 2253`, and
Theorem 8 gives `GW(6; 4, 4) > 328` (`m = 3`, `p = 109`, `z = 0, 1, 2, 0`) and `GW(8; 5, 4) > 1060`
(`m = 4`, `p = 353`, `z = 0, 1, 2, 3`).
-/

namespace GwPower

/-- `c` is a *good exact `r`-colouring of `[1, n]`* for rainbow `k`-term and monochromatic `l`-term
arithmetic progressions: every colour `col : Fin r` occurs on `[1, n]`; no `x, x + d, …, x + (k - 1)d`
in `[1, n]` with `d ≥ 1` has `k` pairwise distinct colours; and no `x, x + d, …, x + (l - 1)d` in
`[1, n]` with `d ≥ 1` has all its terms of one colour. The colouring is a function on all of `ℕ`;
its values outside `[1, n]` play no role. -/
def IsGoodExactColouring (r k l n : ℕ) (c : ℕ → Fin r) : Prop :=
  (∀ col : Fin r, ∃ x, 1 ≤ x ∧ x ≤ n ∧ c x = col) ∧
  (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + (k - 1) * d ≤ n →
    ¬ ∀ i < k, ∀ j < k, i ≠ j → c (x + i * d) ≠ c (x + j * d)) ∧
  (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + (l - 1) * d ≤ n → ¬ ∀ j < l, c (x + j * d) = c x)

/-- `M` has the defining property of the Gallai–van der Waerden number `GW(r; k, l)`
(Mao–Ozeki–Robertson–Wang, JCTA 2023, Def. 1.15): for every `n ≥ M`, every exact `r`-colouring of
`[1, n]` contains a rainbow `k`-term AP or a monochromatic `l`-term AP, that is, no `[1, n]` with
`n ≥ M` has a good exact `r`-colouring. -/
def GWProperty (r k l M : ℕ) : Prop :=
  ∀ n ≥ M, ∀ c : ℕ → Fin r, ¬ IsGoodExactColouring r k l n c

/-- `GW(r; k, l)`: the least `M` with `GWProperty r k l M`. Lean's `sInf` of the empty set of
natural numbers is `0`; the Gallai–van der Waerden theorem says that the set is not empty, but it is
not formalised here, so `lt_GW` assumes that some `M` has the property. -/
noncomputable def GW (r k l : ℕ) : ℕ := sInf {M | GWProperty r k l M}

/-- Condition (i) of Theorems 4 and 8: for every `i ∈ {0, …, m}`, two of the `m` residues `j - i`
(`j ∈ {0, …, m}`, `j ≠ i`) lie in the same `m`-th power class modulo `p`, that is, have the same
value of `a ↦ a ^ ((p - 1) / m)` in `ZMod p`. Equivalently, the `m` residues `j - i` do not lie in
`m` distinct classes. -/
def ConditionI (m p : ℕ) : Prop :=
  ∀ i ≤ m, ∃ j₁ ≤ m, ∃ j₂ ≤ m, j₁ ≠ i ∧ j₂ ≠ i ∧ j₁ ≠ j₂ ∧
    ((j₁ : ZMod p) - i) ^ ((p - 1) / m) = ((j₂ : ZMod p) - i) ^ ((p - 1) / m)

/-- Condition (ii) of Theorems 4 and 8: no `l` consecutive integers `a, a + 1, …, a + l - 1` in
`[1, p - 1]` lie in one `m`-th power class modulo `p`. -/
def ConditionII (m l p : ℕ) : Prop :=
  ∀ a : ℕ, 1 ≤ a → a + (l - 1) ≤ p - 1 →
    ∃ j < l, ((a + j : ℕ) : ZMod p) ^ ((p - 1) / m) ≠ (a : ZMod p) ^ ((p - 1) / m)

/-- The colouring of Theorem 4: `x ↦ (x - 1) ^ ((p - 1) / m)` computed in `ZMod p`. For
`x ≢ 1 (mod p)` this is the `m`-th power class of `x - 1` (an `m`-th root of unity modulo `p`, one of
`m` values when `p ≡ 1 (mod m)`); on the zero class `x ≡ 1 (mod p)` it is `0`, the new colour. -/
def powerColour (p m x : ℕ) : ZMod p := ((x : ZMod p) - 1) ^ ((p - 1) / m)

/-- The colouring of Theorem 8, with colours `ZMod p ⊕ Fin s`. A point `x ≢ 1 (mod p)` gets the
residue colour `Sum.inl ((x - 1) ^ ((p - 1) / m))`, the `m`-th power class of `x - 1`; a point
`x = 1 + kp` of the zero class gets the new colour `Sum.inr (z k)`. -/
def splitColour (p m s : ℕ) (z : ℕ → Fin s) (x : ℕ) : ZMod p ⊕ Fin s :=
  if x % p = 1 then Sum.inr (z ((x - 1) / p)) else Sum.inl (((x : ZMod p) - 1) ^ ((p - 1) / m))

/-- **Theorem 4.** Let `l ≥ 2` and let `p > l` be a prime with `p ≡ 1 (mod m)` satisfying
conditions (i) and (ii). Put `N = (l - 1)p` and `c = powerColour p m`. Then (a) `c` takes exactly
`m + 1` values on `[1, N]`; (b) no `x, x + d, …, x + md` in `[1, N]` with `d ≥ 1` has `m + 1`
pairwise distinct colours; (c) no `x, x + d, …, x + (l - 1)d` in `[1, N]` with `d ≥ 1` has all its
terms of one colour. -/
theorem theorem4 (m l p : ℕ) [Fact p.Prime] (hl : 2 ≤ l) (hlp : l < p) (hpm : p % m = 1)
    (hi : ConditionI m p) (hii : ConditionII m l p) :
    let N := (l - 1) * p
    let c := powerColour p m
    ((Finset.Icc 1 N).image c).card = m + 1 ∧
    (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + m * d ≤ N →
      ¬ ∀ i ≤ m, ∀ j ≤ m, i ≠ j → c (x + i * d) ≠ c (x + j * d)) ∧
    (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + (l - 1) * d ≤ N → ¬ ∀ j < l, c (x + j * d) = c x) := by
  sorry

/-- **Corollary of Theorem 4** (existence form). Under its hypotheses, `[1, (l - 1)p]` has a good
exact `(m + 1)`-colouring for rainbow `(m + 1)`-term and monochromatic `l`-term APs. -/
theorem exists_goodExactColouring (m l p : ℕ) [Fact p.Prime] (hl : 2 ≤ l) (hlp : l < p)
    (hpm : p % m = 1) (hi : ConditionI m p) (hii : ConditionII m l p) :
    ∃ c : ℕ → Fin (m + 1), IsGoodExactColouring (m + 1) (m + 1) l ((l - 1) * p) c := by
  sorry

/-- **Corollary of Theorem 4** (Gallai–van der Waerden form): `GW(m + 1; m + 1, l) > (l - 1)p`.
Every `M` with the defining property of `GW(m + 1; m + 1, l)` exceeds `(l - 1)p`. This form needs no
assumption that such an `M` exists. -/
theorem lt_of_gwProperty (m l p : ℕ) [Fact p.Prime] (hl : 2 ≤ l) (hlp : l < p)
    (hpm : p % m = 1) (hi : ConditionI m p) (hii : ConditionII m l p)
    (M : ℕ) (hM : GWProperty (m + 1) (m + 1) l M) : (l - 1) * p < M := by
  sorry

/-- **Corollary of Theorem 4** for the number itself: `(l - 1)p < GW (m + 1) (m + 1) l`, given that
some `M` has the property (`hex`, the Gallai–van der Waerden theorem, not formalised here). -/
theorem lt_GW (m l p : ℕ) [Fact p.Prime] (hl : 2 ≤ l) (hlp : l < p)
    (hpm : p % m = 1) (hi : ConditionI m p) (hii : ConditionII m l p)
    (hex : ∃ M, GWProperty (m + 1) (m + 1) l M) : (l - 1) * p < GW (m + 1) (m + 1) l := by
  sorry

/-- **Theorem 8.** Let `l ≥ 2` and let `p > l` be a prime with `p ≡ 1 (mod m)` satisfying
conditions (i) and (ii). Let `s ≥ 2` and let `z : ℕ → Fin s` take every value on `{0, …, l - 1}`
(`hz`) with no rainbow `(m + 1)`-term AP `a, a + e, …, a + me` (`e ≥ 1`, `a + me < l`) there
(`hzk`); the values of `z` outside `{0, …, l - 1}` play no role. Put `N = (l - 1)p + 1` and
`c = splitColour p m s z`. Then (a) `c` takes exactly `m + s` values on `[1, N]`; (b) no
`x, x + d, …, x + md` in `[1, N]` with `d ≥ 1` has `m + 1` pairwise distinct colours; (c) no
`x, x + d, …, x + (l - 1)d` in `[1, N]` with `d ≥ 1` has all its terms of one colour. -/
theorem theorem8 (m l p s : ℕ) [Fact p.Prime] (hl : 2 ≤ l) (hlp : l < p) (hpm : p % m = 1)
    (hi : ConditionI m p) (hii : ConditionII m l p) (hs : 2 ≤ s) (z : ℕ → Fin s)
    (hz : ∀ t : Fin s, ∃ k < l, z k = t)
    (hzk : ∀ a e : ℕ, 1 ≤ e → a + m * e < l →
      ¬ ∀ i ≤ m, ∀ j ≤ m, i ≠ j → z (a + i * e) ≠ z (a + j * e)) :
    let N := (l - 1) * p + 1
    let c := splitColour p m s z
    ((Finset.Icc 1 N).image c).card = m + s ∧
    (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + m * d ≤ N →
      ¬ ∀ i ≤ m, ∀ j ≤ m, i ≠ j → c (x + i * d) ≠ c (x + j * d)) ∧
    (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + (l - 1) * d ≤ N → ¬ ∀ j < l, c (x + j * d) = c x) := by
  sorry

/-- **Corollary of Theorem 8** (existence form): `[1, (l - 1)p + 1]` has a good exact
`(m + s)`-colouring for rainbow `(m + 1)`-term and monochromatic `l`-term APs. -/
theorem exists_goodExactColouring_split (m l p s : ℕ) [Fact p.Prime] (hl : 2 ≤ l) (hlp : l < p)
    (hpm : p % m = 1) (hi : ConditionI m p) (hii : ConditionII m l p) (hs : 2 ≤ s)
    (z : ℕ → Fin s) (hz : ∀ t : Fin s, ∃ k < l, z k = t)
    (hzk : ∀ a e : ℕ, 1 ≤ e → a + m * e < l →
      ¬ ∀ i ≤ m, ∀ j ≤ m, i ≠ j → z (a + i * e) ≠ z (a + j * e)) :
    ∃ c : ℕ → Fin (m + s), IsGoodExactColouring (m + s) (m + 1) l ((l - 1) * p + 1) c := by
  sorry

/-- **Corollary of Theorem 8** (Gallai–van der Waerden form): `GW(m + s; m + 1, l) > (l - 1)p + 1`
for every `M` with the defining property; no existence assumption. -/
theorem lt_of_gwProperty_split (m l p s : ℕ) [Fact p.Prime] (hl : 2 ≤ l) (hlp : l < p)
    (hpm : p % m = 1) (hi : ConditionI m p) (hii : ConditionII m l p) (hs : 2 ≤ s)
    (z : ℕ → Fin s) (hz : ∀ t : Fin s, ∃ k < l, z k = t)
    (hzk : ∀ a e : ℕ, 1 ≤ e → a + m * e < l →
      ¬ ∀ i ≤ m, ∀ j ≤ m, i ≠ j → z (a + i * e) ≠ z (a + j * e))
    (M : ℕ) (hM : GWProperty (m + s) (m + 1) l M) : (l - 1) * p + 1 < M := by
  sorry

/-- **Corollary of Theorem 8** for the number itself, given that some `M` has the property. -/
theorem lt_GW_split (m l p s : ℕ) [Fact p.Prime] (hl : 2 ≤ l) (hlp : l < p)
    (hpm : p % m = 1) (hi : ConditionI m p) (hii : ConditionII m l p) (hs : 2 ≤ s)
    (z : ℕ → Fin s) (hz : ∀ t : Fin s, ∃ k < l, z k = t)
    (hzk : ∀ a e : ℕ, 1 ≤ e → a + m * e < l →
      ¬ ∀ i ≤ m, ∀ j ≤ m, i ≠ j → z (a + i * e) ≠ z (a + j * e))
    (hex : ∃ M, GWProperty (m + s) (m + 1) l M) :
    (l - 1) * p + 1 < GW (m + s) (m + 1) l := by
  sorry

/-- **Instance** of Theorem 4 with `m = 3`, `l = 4`, `p = 109`: `GW(4; 4, 4) > 327`. -/
theorem gw_4_4_4 (M : ℕ) (hM : GWProperty 4 4 4 M) : 327 < M := by
  sorry

/-- **Instance** of Theorem 4 with `m = 4`, `l = 4`, `p = 353`: `GW(5; 5, 4) > 1059`. -/
theorem gw_5_5_4 (M : ℕ) (hM : GWProperty 5 5 4 M) : 1059 < M := by
  sorry

/-- **Instance** of Theorem 4 with `m = 5`, `l = 4`, `p = 751`: `GW(6; 6, 4) > 2253`. -/
theorem gw_6_6_4 (M : ℕ) (hM : GWProperty 6 6 4 M) : 2253 < M := by
  sorry

/-- **Instance** of Theorem 8 with `m = 3`, `l = 4`, `p = 109`, `s = 3`, `z = 0, 1, 2, 0`:
`GW(6; 4, 4) > 328`. -/
theorem gw_6_4_4 (M : ℕ) (hM : GWProperty 6 4 4 M) : 328 < M := by
  sorry

/-- **Instance** of Theorem 8 with `m = 4`, `l = 4`, `p = 353`, `s = 4`, `z = 0, 1, 2, 3`:
`GW(8; 5, 4) > 1060`. -/
theorem gw_8_5_4 (M : ℕ) (hM : GWProperty 8 5 4 M) : 1060 < M := by
  sorry

end GwPower
