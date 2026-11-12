module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Definitions used by the proof

These are the definitions of `Challenge.lean`, with the same imports and the same text, so that the
proof is about exactly the notions the statement uses (Comparator checks that the declarations
agree). See `Challenge.lean` for the mathematical account.
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

end GwPower
