module

public import GwPower.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime

public section

/-!
# Proofs of Theorems 4 and 8

The lemmas behind `Solution.lean`. Write `e = (p - 1)/m` and call `a ^ e` (in `ZMod p`) the class
of `a`.

* `exists_good_of_card` relabels a colouring with any colour type that takes exactly `r` values on
  `[1, n]` as a colouring with colours `Fin r`; `lt_of_good` turns a good exact colouring of
  `[1, n]` into `n < M` for every `M` with the GW property.
* Section `Power` (Theorem 4, `powerColour`): `card_classes` (the nonzero residues have exactly `m`
  classes), `card_image` (part (a)), `no_rainbow` (part (b), for every `x` and `d`), `no_mono_core`
  and `no_mono` (part (c)).
* Section `Split` (Theorem 8, `splitColour`): `split_card_image`, `split_no_rainbow` and
  `split_no_mono`, which reduce to the lemmas of section `Power` when at most one term of a
  progression lies in the zero class.
* `powerColour_isGood`, `splitColour_isGood`: the good exact colourings with colours `Fin (m + 1)`
  and `Fin (m + s)`.
* Section `Instances`: conditions (i) and (ii) for `(m, l, p) = (3, 4, 109)`, `(4, 4, 353)` and
  `(5, 4, 751)`, checked by `decide` through natural-number arithmetic (`conditionI_of_nat`,
  `conditionII_of_nat`), and the five good exact colourings behind the instances of
  `Challenge.lean`.
-/

namespace GwPower

/-- A good exact colouring of `[1, n]` forces every GW threshold above `n`. -/
theorem lt_of_good {r k l n : ℕ} {c : ℕ → Fin r} (hc : IsGoodExactColouring r k l n c) {M : ℕ}
    (hM : GWProperty r k l M) : n < M := by
  by_contra h
  exact hM n (not_lt.mp h) c hc

/-- Relabelling the colours. A colouring `c` with values in any type that takes exactly `r`
values on `[1, n]` and has no rainbow `k`-term and no monochromatic `l`-term AP in `[1, n]` gives a
good exact `r`-colouring of `[1, n]` with colours `Fin r`. -/
theorem exists_good_of_card {α : Type*} [DecidableEq α] {r k l n : ℕ} (hr : 0 < r) (c : ℕ → α)
    (hcard : ((Finset.Icc 1 n).image c).card = r)
    (hrb : ∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + (k - 1) * d ≤ n →
      ¬ ∀ i < k, ∀ j < k, i ≠ j → c (x + i * d) ≠ c (x + j * d))
    (hmono : ∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + (l - 1) * d ≤ n → ¬ ∀ j < l, c (x + j * d) = c x) :
    ∃ c' : ℕ → Fin r, IsGoodExactColouring r k l n c' := by
  set S := (Finset.Icc 1 n).image c with hS
  let E : S ≃ Fin r := Finset.equivFinOfCardEq hcard
  let f : α → Fin r := fun v => if hv : v ∈ S then E ⟨v, hv⟩ else ⟨0, hr⟩
  have hf : ∀ v (hv : v ∈ S), f v = E ⟨v, hv⟩ := fun v hv => dite_eq_left hv
  have hmem : ∀ y, 1 ≤ y → y ≤ n → c y ∈ S := fun y h1 h2 =>
    Finset.mem_image_of_mem c (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  refine ⟨fun x => f (c x), ?_, ?_, ?_⟩
  · intro col
    obtain ⟨⟨v, hv⟩, rfl⟩ := E.surjective col
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    rw [Finset.mem_Icc] at hx
    exact ⟨x, hx.1, hx.2, hf _ hv⟩
  · intro x d hx hd hN hall
    apply hrb x d hx hd hN
    intro i hi j hj hij heq
    exact hall i hi j hj hij (by simp only [heq])
  · intro x d hx hd hN hall
    apply hmono x d hx hd hN
    intro j hj
    have hjd : j * d ≤ (l - 1) * d := Nat.mul_le_mul_right d (by omega)
    have h := hall j hj
    simp only at h
    rw [hf _ (hmem _ (by omega) (by omega)), hf _ (hmem _ hx (by omega))] at h
    exact congrArg Subtype.val (E.injective h)

section Power

variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}

theorem m_pos (hpm : p % m = 1) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    rw [Nat.mod_zero] at hpm
    exact absurd hpm hp.out.one_lt.ne'
  · exact h

omit hp in
theorem dvd_sub_one (hpm : p % m = 1) : m ∣ p - 1 :=
  ⟨p / m, by have h := Nat.div_add_mod p m; rw [hpm] at h; omega⟩

omit hp in
theorem exp_mul (hpm : p % m = 1) : (p - 1) / m * m = p - 1 :=
  Nat.div_mul_cancel (dvd_sub_one hpm)

/-- The exponent `(p - 1)/m` is positive. -/
theorem exp_pos (hpm : p % m = 1) : 0 < (p - 1) / m := by
  have h1 := exp_mul (p := p) hpm
  have h2 : 1 < p := hp.out.one_lt
  rcases Nat.eq_zero_or_pos ((p - 1) / m) with h | h
  · rw [h, Nat.zero_mul] at h1
    omega
  · exact h

/-- The class `a ^ ((p - 1)/m)` of a nonzero `a` is an `m`-th root of unity. -/
private theorem mem_roots (hpm : p % m = 1) {a : ZMod p} (ha : a ≠ 0) :
    a ^ ((p - 1) / m) ∈ Polynomial.nthRootsFinset m (1 : ZMod p) := by
  rw [Polynomial.mem_nthRootsFinset (m_pos hpm), ← pow_mul, exp_mul hpm,
    ZMod.pow_card_sub_one_eq_one ha]

/-- There are at most `n` roots of `X ^ n = b`. -/
private theorem card_roots_le (n : ℕ) (b : ZMod p) : (Polynomial.nthRootsFinset n b).card ≤ n := by
  classical
  rw [Polynomial.nthRootsFinset_def]
  exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)

/-- The `m`-th power classes of the nonzero residues: `{a ^ ((p - 1)/m) : a ≠ 0}`. -/
abbrev classes (p m : ℕ) [NeZero p] : Finset (ZMod p) :=
  (Finset.univ.erase (0 : ZMod p)).image (fun a : ZMod p => a ^ ((p - 1) / m))

theorem zero_notMem_classes : (0 : ZMod p) ∉ classes p m := by
  intro h0
  obtain ⟨a, ha, h⟩ := Finset.mem_image.mp h0
  exact pow_ne_zero _ (Finset.ne_of_mem_erase ha) h

theorem pow_mem_classes {a : ZMod p} (ha : a ≠ 0) : a ^ ((p - 1) / m) ∈ classes p m :=
  Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩)

/-- There are exactly `m` classes: at least `m`, since each class contains at most
`(p - 1)/m` of the `p - 1` nonzero residues, and at most `m`, since they are `m`-th roots of
unity. -/
theorem card_classes (hpm : p % m = 1) : (classes p m).card = m := by
  classical
  have he : 0 < (p - 1) / m := exp_pos hpm
  apply le_antisymm
  · refine (Finset.card_le_card ?_).trans (card_roots_le m (1 : ZMod p))
    intro v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    exact mem_roots hpm (Finset.ne_of_mem_erase ha)
  · have h1 : (Finset.univ.erase (0 : ZMod p)).card ≤ (p - 1) / m * (classes p m).card := by
      apply Finset.card_le_mul_card_image
      intro b _
      refine (Finset.card_le_card (t := Polynomial.nthRootsFinset ((p - 1) / m) b) ?_).trans
        (card_roots_le _ b)
      intro a ha
      rw [Finset.mem_filter] at ha
      exact (Polynomial.mem_nthRootsFinset he b).mpr ha.2
    have h2 : (Finset.univ.erase (0 : ZMod p)).card = p - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
    rw [h2] at h1
    have h3 : (p - 1) / m * m ≤ (p - 1) / m * (classes p m).card := by
      rw [exp_mul hpm]; exact h1
    exact Nat.le_of_mul_le_mul_left h3 he

/-- Part (a): the colouring takes exactly `m + 1` values on `[1, (l - 1)p]`, namely `0` and the
`m` classes. -/
theorem card_image (hl : 2 ≤ l) (hpm : p % m = 1) :
    ((Finset.Icc 1 ((l - 1) * p)).image (powerColour p m)).card = m + 1 := by
  classical
  have hp1 : 1 < p := hp.out.one_lt
  have he : 0 < (p - 1) / m := exp_pos hpm
  have hpN : p ≤ (l - 1) * p := Nat.le_mul_of_pos_left p (by omega)
  have himage : (Finset.Icc 1 ((l - 1) * p)).image (powerColour p m) = insert 0 (classes p m) := by
    apply Finset.Subset.antisymm
    · intro v hv
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hv
      rw [Finset.mem_insert]
      by_cases hx : (x : ZMod p) - 1 = 0
      · left
        unfold powerColour
        rw [hx, zero_pow he.ne']
      · exact Or.inr (pow_mem_classes hx)
    · intro v hv
      rw [Finset.mem_insert] at hv
      rw [Finset.mem_image]
      rcases hv with rfl | hv
      · refine ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, ?_⟩
        unfold powerColour
        rw [Nat.cast_one, sub_self, zero_pow he.ne']
      · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hv
        have ha := ZMod.val_lt a
        refine ⟨a.val + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
        unfold powerColour
        rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, ZMod.natCast_zmod_val]
  rw [himage, Finset.card_insert_of_notMem zero_notMem_classes, card_classes hpm]

/-- Part (b): no rainbow `(m + 1)`-term AP, for any `x` and `d`. -/
theorem no_rainbow (hpm : p % m = 1)
    (hi : ∀ i ≤ m, ∃ j₁ ≤ m, ∃ j₂ ≤ m, j₁ ≠ i ∧ j₂ ≠ i ∧ j₁ ≠ j₂ ∧
      ((j₁ : ZMod p) - i) ^ ((p - 1) / m) = ((j₂ : ZMod p) - i) ^ ((p - 1) / m))
    (x d : ℕ) :
    ¬ ∀ i ≤ m, ∀ j ≤ m, i ≠ j → powerColour p m (x + i * d) ≠ powerColour p m (x + j * d) := by
  intro hall
  by_cases hz : ∃ i ≤ m, ((x + i * d : ℕ) : ZMod p) = 1
  · -- a term `x + i d` lies in the zero class: the others have residues `(j - i) d`
    obtain ⟨i, him, hi1⟩ := hz
    obtain ⟨j₁, hj₁, j₂, hj₂, -, -, h12, heq⟩ := hi i him
    apply hall j₁ hj₁ j₂ hj₂ h12
    have key : ∀ j : ℕ, powerColour p m (x + j * d) =
        ((j : ZMod p) - i) ^ ((p - 1) / m) * (d : ZMod p) ^ ((p - 1) / m) := by
      intro j
      unfold powerColour
      rw [← mul_pow]
      congr 1
      push_cast at hi1 ⊢
      linear_combination hi1
    rw [key j₁, key j₂, heq]
  · -- no term lies in the zero class: `m + 1` values among the `m`-th roots of unity
    push Not at hz
    have hmaps : Set.MapsTo (fun i => powerColour p m (x + i * d)) (Finset.range (m + 1) : Set ℕ)
        (Polynomial.nthRootsFinset m (1 : ZMod p) : Set (ZMod p)) := by
      intro i hi
      have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      exact mem_roots hpm (sub_ne_zero.mpr (hz i him))
    have hlt : (Polynomial.nthRootsFinset m (1 : ZMod p)).card < (Finset.range (m + 1)).card := by
      rw [Finset.card_range]
      exact Nat.lt_succ_of_le (card_roots_le m (1 : ZMod p))
    obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
    exact hall i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) j
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hij heq

/-- The core of part (c): if `p ∤ d`, the power colours of `x, x + d, …, x + (l - 1)d` are not
all equal. -/
theorem no_mono_core (hl : 2 ≤ l) (hlp : l < p) (hpm : p % m = 1)
    (hii : ∀ a : ℕ, 1 ≤ a → a + (l - 1) ≤ p - 1 →
      ∃ j < l, ((a + j : ℕ) : ZMod p) ^ ((p - 1) / m) ≠ (a : ZMod p) ^ ((p - 1) / m))
    (x d : ℕ) (hd0 : (d : ZMod p) ≠ 0) :
    ¬ ∀ j < l, powerColour p m (x + j * d) = powerColour p m x := by
  intro hall
  have he : 0 < (p - 1) / m := exp_pos hpm
  -- write `x - 1 ≡ A d (mod p)`; the term `x + j d` has residue `(A + j) d`
  obtain ⟨A, hAD⟩ : ∃ A : ZMod p, A * (d : ZMod p) = (x : ZMod p) - 1 :=
    ⟨_, div_mul_cancel₀ _ hd0⟩
  have hterm : ∀ j : ℕ, powerColour p m (x + j * d) = ((A + j) * d) ^ ((p - 1) / m) := by
    intro j
    unfold powerColour
    congr 1
    push_cast
    linear_combination -hAD
  have hcol0 : powerColour p m x = (A * d) ^ ((p - 1) / m) := by
    unfold powerColour
    rw [hAD]
  by_cases hz : ∃ i < l, A + (i : ZMod p) = 0
  · -- one term `x + i d` in the zero class has colour `0`; another term has a nonzero colour
    obtain ⟨i, hil, hAi⟩ := hz
    obtain ⟨j, hjl, hji⟩ : ∃ j < l, j ≠ i :=
      ⟨if i = 0 then 1 else 0, by split_ifs <;> omega, by split_ifs <;> omega⟩
    have hci : powerColour p m (x + i * d) = 0 := by
      rw [hterm i, hAi, zero_mul, zero_pow he.ne']
    have hcj : powerColour p m (x + j * d) ≠ 0 := by
      rw [hterm j]
      refine pow_ne_zero _ (mul_ne_zero ?_ hd0)
      intro h
      have hji' : ((j : ℕ) : ZMod p) = (i : ZMod p) := by linear_combination h - hAi
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega : j < p),
        Nat.mod_eq_of_lt (by omega : i < p)] at hji'
      exact hji hji'
    exact hcj (by rw [hall j hjl, ← hall i hil, hci])
  · -- no term in the zero class: `A = a` with `a, a + 1, …, a + l - 1` in `[1, p - 1]`
    push Not at hz
    obtain ⟨a, ha_lt, rfl⟩ : ∃ a : ℕ, a < p ∧ (a : ZMod p) = A :=
      ⟨A.val, ZMod.val_lt A, ZMod.natCast_zmod_val A⟩
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · exfalso
        apply hz 0 (by omega)
        rw [h]
        simp
      · exact h
    have hal : a + (l - 1) ≤ p - 1 := by
      by_contra hcon
      apply hz (p - a) (by omega)
      rw [← Nat.cast_add, show a + (p - a) = p by omega, ZMod.natCast_self]
    obtain ⟨j, hjl, hne⟩ := hii a ha1 hal
    apply hne
    have h := hall j hjl
    rw [hterm j, hcol0, mul_pow, mul_pow] at h
    push_cast
    exact mul_right_cancel₀ (pow_ne_zero _ hd0) h

/-- Part (c): no monochromatic `l`-term AP in `[1, (l - 1)p]`. -/
theorem no_mono (hl : 2 ≤ l) (hlp : l < p) (hpm : p % m = 1)
    (hii : ∀ a : ℕ, 1 ≤ a → a + (l - 1) ≤ p - 1 →
      ∃ j < l, ((a + j : ℕ) : ZMod p) ^ ((p - 1) / m) ≠ (a : ZMod p) ^ ((p - 1) / m))
    (x d : ℕ) (hx : 1 ≤ x) (hd : 1 ≤ d) (hN : x + (l - 1) * d ≤ (l - 1) * p) :
    ¬ ∀ j < l, powerColour p m (x + j * d) = powerColour p m x := by
  -- `p ∤ d`, since `(l - 1)d ≤ (l - 1)p - 1`
  have hd0 : (d : ZMod p) ≠ 0 := by
    intro h0
    have hpd : p ≤ d := Nat.le_of_dvd hd ((ZMod.natCast_eq_zero_iff d p).mp h0)
    have : (l - 1) * p ≤ (l - 1) * d := Nat.mul_le_mul_left _ hpd
    omega
  exact no_mono_core hl hlp hpm hii x d hd0

end Power

section Split

/-! ## Theorem 8: the zero class split by a colouring `z` -/

variable {p : ℕ} [hp : Fact p.Prime] {m s l : ℕ} {z : ℕ → Fin s}

theorem mod_eq_one_iff (y : ℕ) : y % p = 1 ↔ (y : ZMod p) = 1 := by
  have h := ZMod.natCast_eq_natCast_iff' y 1 p
  rw [Nat.cast_one, Nat.mod_eq_of_lt hp.out.one_lt] at h
  exact h.symm

omit hp in
theorem eq_one_add_mul_of_mod {x : ℕ} (hx : x % p = 1) : x = 1 + p * (x / p) := by
  have := Nat.mod_add_div x p
  rw [hx] at this
  exact this.symm

theorem m_lt_p (hpm : p % m = 1) : m < p := by
  have h1 : 1 < p := hp.out.one_lt
  have := Nat.le_of_dvd (by omega) (dvd_sub_one hpm)
  omega

theorem powerColour_eq_zero (hpm : p % m = 1) {x : ℕ} (hx : x % p = 1) : powerColour p m x = 0 := by
  unfold powerColour
  rw [(mod_eq_one_iff x).mp hx, sub_self, zero_pow (exp_pos hpm).ne']

theorem powerColour_ne_zero {x : ℕ} (hx : x % p ≠ 1) : powerColour p m x ≠ 0 := by
  unfold powerColour
  refine pow_ne_zero _ (sub_ne_zero.mpr ?_)
  rwa [Ne, ← mod_eq_one_iff]

omit hp in
theorem splitColour_of_mod_ne {x : ℕ} (hx : x % p ≠ 1) :
    splitColour p m s z x = Sum.inl (powerColour p m x) := by
  unfold splitColour powerColour
  rw [ite_eq_right hx]

omit hp in
theorem splitColour_of_mod_eq {x : ℕ} (hx : x % p = 1) :
    splitColour p m s z x = Sum.inr (z ((x - 1) / p)) := by
  unfold splitColour
  rw [ite_eq_left hx]

theorem splitColour_one_add_mul (k : ℕ) : splitColour p m s z (1 + p * k) = Sum.inr (z k) := by
  have hp1 : 1 < p := hp.out.one_lt
  have h1 : (1 + p * k) % p = 1 := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp1]
  rw [splitColour_of_mod_eq h1, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left k (by omega)]

/-- Part (a) of Theorem 8: the colouring takes exactly `m + s` values on `[1, (l - 1)p + 1]`, the
`m` classes and the `s` colours of `z`. -/
theorem split_card_image (hl : 2 ≤ l) (hpm : p % m = 1) (hz : ∀ t : Fin s, ∃ k < l, z k = t) :
    ((Finset.Icc 1 ((l - 1) * p + 1)).image (splitColour p m s z)).card = m + s := by
  classical
  have hp1 : 1 < p := hp.out.one_lt
  have hpN : p ≤ (l - 1) * p := Nat.le_mul_of_pos_left p (by omega)
  have himage : (Finset.Icc 1 ((l - 1) * p + 1)).image (splitColour p m s z) =
      (classes p m).disjSum (Finset.univ : Finset (Fin s)) := by
    apply Finset.Subset.antisymm
    · intro v hv
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hv
      by_cases hx : x % p = 1
      · rw [splitColour_of_mod_eq hx, Finset.inr_mem_disjSum]
        exact Finset.mem_univ _
      · rw [splitColour_of_mod_ne hx, Finset.inl_mem_disjSum]
        exact pow_mem_classes (sub_ne_zero.mpr (by rwa [Ne, ← mod_eq_one_iff]))
    · intro v hv
      rw [Finset.mem_image]
      rcases v with v | t
      · rw [Finset.inl_mem_disjSum] at hv
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
        have ha0 : a ≠ 0 := Finset.ne_of_mem_erase ha
        have hav := ZMod.val_lt a
        have hx : (a.val + 1) % p ≠ 1 := by
          rw [Ne, mod_eq_one_iff, Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
          intro h
          exact ha0 (by linear_combination h)
        refine ⟨a.val + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
        rw [splitColour_of_mod_ne hx]
        unfold powerColour
        rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, ZMod.natCast_zmod_val]
      · obtain ⟨k, hk, rfl⟩ := hz t
        have hkp : p * k ≤ (l - 1) * p := by
          rw [Nat.mul_comm]; exact Nat.mul_le_mul_right p (by omega)
        exact ⟨1 + p * k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, splitColour_one_add_mul k⟩
  rw [himage, Finset.card_disjSum, card_classes hpm, Finset.card_univ, Fintype.card_fin]

/-- Part (b) of Theorem 8: no rainbow `(m + 1)`-term AP in `[1, (l - 1)p + 1]`. -/
theorem split_no_rainbow (hl : 2 ≤ l) (hpm : p % m = 1)
    (hi : ∀ i ≤ m, ∃ j₁ ≤ m, ∃ j₂ ≤ m, j₁ ≠ i ∧ j₂ ≠ i ∧ j₁ ≠ j₂ ∧
      ((j₁ : ZMod p) - i) ^ ((p - 1) / m) = ((j₂ : ZMod p) - i) ^ ((p - 1) / m))
    (hzk : ∀ a e : ℕ, 1 ≤ e → a + m * e < l →
      ¬ ∀ i ≤ m, ∀ j ≤ m, i ≠ j → z (a + i * e) ≠ z (a + j * e))
    (x d : ℕ) (hd : 1 ≤ d) (hN : x + m * d ≤ (l - 1) * p + 1) :
    ¬ ∀ i ≤ m, ∀ j ≤ m, i ≠ j →
      splitColour p m s z (x + i * d) ≠ splitColour p m s z (x + j * d) := by
  intro hall
  have hp1 : 1 < p := hp.out.one_lt
  have hmp : m < p := m_lt_p hpm
  by_cases h2 : ∃ i ≤ m, ∃ j ≤ m, i ≠ j ∧ (x + i * d) % p = 1 ∧ (x + j * d) % p = 1
  · -- two terms in the zero class: `p ∣ d`, and the AP lies in the zero class
    obtain ⟨i, hi', j, hj, hij, hxi, hxj⟩ := h2
    have hd0 : (d : ZMod p) = 0 := by
      rw [mod_eq_one_iff] at hxi hxj
      push_cast at hxi hxj
      have h : ((j : ZMod p) - i) * d = 0 := by linear_combination hxj - hxi
      rcases mul_eq_zero.mp h with h | h
      · exfalso
        apply hij
        have h' : ((j : ℕ) : ZMod p) = (i : ZMod p) := sub_eq_zero.mp h
        rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)] at h'
        exact h'.symm
      · exact h
    obtain ⟨e, rfl⟩ := (ZMod.natCast_eq_zero_iff d p).mp hd0
    have he : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h | h
      · subst h; simp at hd
      · exact h
    have hx1 : x % p = 1 := by
      have h := hxi
      rwa [Nat.mul_comm p e, ← Nat.mul_assoc, Nat.add_mul_mod_self_right] at h
    obtain ⟨k, rfl⟩ : ∃ k, x = 1 + p * k := ⟨x / p, eq_one_add_mul_of_mod hx1⟩
    have hterm : ∀ t, 1 + p * k + t * (p * e) = 1 + p * (k + t * e) := by intro t; ring
    have hkm : k + m * e < l := by
      rw [hterm m] at hN
      have h1 : p * (k + m * e) ≤ p * (l - 1) := by rw [Nat.mul_comm p (l - 1)]; omega
      have := Nat.le_of_mul_le_mul_left h1 (by omega : 0 < p)
      omega
    apply hzk k e he hkm
    intro i' hi'' j' hj' hij' heq
    apply hall i' hi'' j' hj' hij'
    rw [hterm i', hterm j', splitColour_one_add_mul, splitColour_one_add_mul, heq]
  · -- at most one term in the zero class: the AP would be rainbow for `powerColour`
    push Not at h2
    apply no_rainbow hpm hi x d
    intro i hi' j hj hij heq
    by_cases hxi : (x + i * d) % p = 1
    · rw [powerColour_eq_zero hpm hxi] at heq
      exact powerColour_ne_zero (h2 i hi' j hj hij hxi) heq.symm
    · by_cases hxj : (x + j * d) % p = 1
      · rw [powerColour_eq_zero hpm hxj] at heq
        exact powerColour_ne_zero hxi heq
      · apply hall i hi' j hj hij
        rw [splitColour_of_mod_ne hxi, splitColour_of_mod_ne hxj, heq]

/-- Part (c) of Theorem 8: no monochromatic `l`-term AP in `[1, (l - 1)p + 1]`. -/
theorem split_no_mono (hl : 2 ≤ l) (hlp : l < p) (hpm : p % m = 1)
    (hii : ∀ a : ℕ, 1 ≤ a → a + (l - 1) ≤ p - 1 →
      ∃ j < l, ((a + j : ℕ) : ZMod p) ^ ((p - 1) / m) ≠ (a : ZMod p) ^ ((p - 1) / m))
    (hs : 2 ≤ s) (hz : ∀ t : Fin s, ∃ k < l, z k = t)
    (x d : ℕ) (hx : 1 ≤ x) (hd : 1 ≤ d) (hN : x + (l - 1) * d ≤ (l - 1) * p + 1) :
    ¬ ∀ j < l, splitColour p m s z (x + j * d) = splitColour p m s z x := by
  intro hall
  have hp1 : 1 < p := hp.out.one_lt
  by_cases hd0 : (d : ZMod p) = 0
  · -- `p ∣ d` forces `d = p` and `x = 1`: the AP is the zero class, coloured by `z`
    obtain ⟨e, rfl⟩ := (ZMod.natCast_eq_zero_iff d p).mp hd0
    have he : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h | h
      · subst h; simp at hd
      · exact h
    have h1 : (l - 1) * (p * e) ≤ (l - 1) * (p * 1) := by rw [Nat.mul_one]; omega
    have h2 : p * e ≤ p * 1 := Nat.le_of_mul_le_mul_left h1 (by omega)
    have he1 : e = 1 := by have := Nat.le_of_mul_le_mul_left h2 (by omega : 0 < p); omega
    subst he1
    have hx1 : x = 1 := by rw [Nat.mul_one] at hN; omega
    subst hx1
    have hcol : ∀ j, splitColour p m s z (1 + j * (p * 1)) = Sum.inr (z j) := by
      intro j
      rw [show 1 + j * (p * 1) = 1 + p * j by ring]
      exact splitColour_one_add_mul j
    obtain ⟨k₀, hk₀, hzk₀⟩ := hz ⟨0, by omega⟩
    obtain ⟨k₁, hk₁, hzk₁⟩ := hz ⟨1, by omega⟩
    have h := (hall k₀ hk₀).trans (hall k₁ hk₁).symm
    rw [hcol, hcol, hzk₀, hzk₁] at h
    simp at h
  · -- `p ∤ d`: no term lies in the zero class, and the power colours are constant
    have hx0 : x % p ≠ 1 := by
      intro hx1
      have h1 := hall 1 (by omega)
      by_cases hx1' : (x + 1 * d) % p = 1
      · apply hd0
        rw [mod_eq_one_iff] at hx1 hx1'
        push_cast at hx1'
        linear_combination hx1' - hx1
      · rw [splitColour_of_mod_ne hx1', splitColour_of_mod_eq hx1] at h1
        exact Sum.inl_ne_inr h1
    have hpc : ∀ j < l, powerColour p m (x + j * d) = powerColour p m x := by
      intro j hj
      have h := hall j hj
      rw [splitColour_of_mod_ne hx0] at h
      by_cases hj1 : (x + j * d) % p = 1
      · rw [splitColour_of_mod_eq hj1] at h
        exact absurd h Sum.inr_ne_inl
      · rw [splitColour_of_mod_ne hj1] at h
        exact Sum.inl_injective h
    exact no_mono_core hl hlp hpm hii x d hd0 hpc

end Split

/-! ## Good exact colourings with colours `Fin r` -/

/-- Theorem 4 gives a good exact `(m + 1)`-colouring of `[1, (l - 1)p]` for `(m + 1, l)`. -/
theorem powerColour_isGood (m l p : ℕ) [Fact p.Prime] (hl : 2 ≤ l) (hlp : l < p)
    (hpm : p % m = 1) (hi : ConditionI m p) (hii : ConditionII m l p) :
    ∃ c : ℕ → Fin (m + 1), IsGoodExactColouring (m + 1) (m + 1) l ((l - 1) * p) c := by
  refine exists_good_of_card (Nat.succ_pos m) (powerColour p m) (card_image hl hpm) ?_
    (fun x d hx hd hN => no_mono hl hlp hpm hii x d hx hd hN)
  intro x d _ _ _ hall
  exact no_rainbow hpm hi x d fun i hi' j hj hij =>
    hall i (Nat.lt_succ_of_le hi') j (Nat.lt_succ_of_le hj) hij

/-- Theorem 8 gives a good exact `(m + s)`-colouring of `[1, (l - 1)p + 1]` for `(m + 1, l)`. -/
theorem splitColour_isGood (m l p s : ℕ) [Fact p.Prime] (hl : 2 ≤ l) (hlp : l < p)
    (hpm : p % m = 1) (hi : ConditionI m p) (hii : ConditionII m l p) (hs : 2 ≤ s)
    (z : ℕ → Fin s) (hz : ∀ t : Fin s, ∃ k < l, z k = t)
    (hzk : ∀ a e : ℕ, 1 ≤ e → a + m * e < l →
      ¬ ∀ i ≤ m, ∀ j ≤ m, i ≠ j → z (a + i * e) ≠ z (a + j * e)) :
    ∃ c : ℕ → Fin (m + s), IsGoodExactColouring (m + s) (m + 1) l ((l - 1) * p + 1) c := by
  refine exists_good_of_card (by omega) (splitColour p m s z) (split_card_image hl hpm hz) ?_
    (fun x d hx hd hN => split_no_mono hl hlp hpm hii hs hz x d hx hd hN)
  intro x d _ hd hN hall
  exact split_no_rainbow hl hpm hi hzk x d hd (by simpa using hN) fun i hi' j hj hij =>
    hall i (Nat.lt_succ_of_le hi') j (Nat.lt_succ_of_le hj) hij

/-! ## Instances

Conditions (i) and (ii) for a given `(m, l, p)` are finite computations; `conditionI_of_nat` and
`conditionII_of_nat` restate them with natural-number arithmetic (`a ^ ((p - 1)/m) % p`), which
`decide` evaluates in the kernel. -/

section Instances

theorem conditionI_of_nat {m p : ℕ} [Fact p.Prime] (hmp : m < p)
    (h : ∀ i ≤ m, ∃ j₁ ≤ m, ∃ j₂ ≤ m, j₁ ≠ i ∧ j₂ ≠ i ∧ j₁ ≠ j₂ ∧
      (j₁ + p - i) ^ ((p - 1) / m) % p = (j₂ + p - i) ^ ((p - 1) / m) % p) :
    ConditionI m p := by
  intro i hi
  obtain ⟨j₁, hj₁, j₂, hj₂, h1, h2, h12, heq⟩ := h i hi
  refine ⟨j₁, hj₁, j₂, hj₂, h1, h2, h12, ?_⟩
  have key : ∀ j : ℕ, (((j + p - i) ^ ((p - 1) / m) : ℕ) : ZMod p) =
      ((j : ZMod p) - i) ^ ((p - 1) / m) := by
    intro j
    rw [Nat.cast_pow, Nat.add_sub_assoc (by omega : i ≤ p), Nat.cast_add,
      Nat.cast_sub (by omega : i ≤ p), ZMod.natCast_self]
    ring
  rw [← key j₁, ← key j₂]
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr heq

theorem conditionII_of_nat {m l p : ℕ} [Fact p.Prime]
    (h : ∀ a < p, 1 ≤ a → a + (l - 1) ≤ p - 1 →
      ∃ j < l, (a + j) ^ ((p - 1) / m) % p ≠ a ^ ((p - 1) / m) % p) :
    ConditionII m l p := by
  intro a ha hal
  obtain ⟨j, hj, hne⟩ := h a (by omega) ha hal
  refine ⟨j, hj, fun heq => hne ?_⟩
  rw [← Nat.cast_pow, ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff'] at heq
  exact heq

instance fact_prime_109 : Fact (Nat.Prime 109) := ⟨by norm_num⟩
instance fact_prime_353 : Fact (Nat.Prime 353) := ⟨by norm_num⟩
instance fact_prime_751 : Fact (Nat.Prime 751) := ⟨by norm_num⟩

theorem conditionI_3_109 : ConditionI 3 109 := conditionI_of_nat (by norm_num) (by decide)
theorem conditionII_3_4_109 : ConditionII 3 4 109 := conditionII_of_nat (by decide)
theorem conditionI_4_353 : ConditionI 4 353 := conditionI_of_nat (by norm_num) (by decide)
theorem conditionII_4_4_353 : ConditionII 4 4 353 := conditionII_of_nat (by decide +kernel)
theorem conditionI_5_751 : ConditionI 5 751 := conditionI_of_nat (by norm_num) (by decide)
theorem conditionII_5_4_751 : ConditionII 5 4 751 := conditionII_of_nat (by decide +kernel)

/-- `z = 0, 1, 2, 0` on `{0, 1, 2, 3}` (three colours, no rainbow 4-term AP). -/
def z0120 : ℕ → Fin 3 := fun k => [0, 1, 2, 0].getD k 0

/-- `z = 0, 1, 2, 3` on `{0, 1, 2, 3}` (four colours; no 5-term AP fits in `{0, 1, 2, 3}`). -/
def z0123 : ℕ → Fin 4 := fun k => [0, 1, 2, 3].getD k 0

/-- Theorem 4, `m = 3`, `l = 4`, `p = 109`: a good exact 4-colouring of `[1, 327]`. -/
theorem good_4_4_4 : ∃ c : ℕ → Fin 4, IsGoodExactColouring 4 4 4 327 c :=
  powerColour_isGood 3 4 109 (by norm_num) (by norm_num) (by norm_num) conditionI_3_109
    conditionII_3_4_109

/-- Theorem 4, `m = 4`, `l = 4`, `p = 353`: a good exact 5-colouring of `[1, 1059]`. -/
theorem good_5_5_4 : ∃ c : ℕ → Fin 5, IsGoodExactColouring 5 5 4 1059 c :=
  powerColour_isGood 4 4 353 (by norm_num) (by norm_num) (by norm_num) conditionI_4_353
    conditionII_4_4_353

/-- Theorem 4, `m = 5`, `l = 4`, `p = 751`: a good exact 6-colouring of `[1, 2253]`. -/
theorem good_6_6_4 : ∃ c : ℕ → Fin 6, IsGoodExactColouring 6 6 4 2253 c :=
  powerColour_isGood 5 4 751 (by norm_num) (by norm_num) (by norm_num) conditionI_5_751
    conditionII_5_4_751

/-- Theorem 8, `m = 3`, `l = 4`, `p = 109`, `z = 0, 1, 2, 0`: a good exact 6-colouring of
`[1, 328]` for rainbow 4-term and monochromatic 4-term APs. -/
theorem good_6_4_4 : ∃ c : ℕ → Fin 6, IsGoodExactColouring 6 4 4 328 c :=
  splitColour_isGood 3 4 109 3 (by norm_num) (by norm_num) (by norm_num) conditionI_3_109
    conditionII_3_4_109 (by norm_num) z0120 (by decide) (by
      intro a e he h
      obtain ⟨rfl, rfl⟩ : a = 0 ∧ e = 1 := by omega
      decide)

/-- Theorem 8, `m = 4`, `l = 4`, `p = 353`, `z = 0, 1, 2, 3`: a good exact 8-colouring of
`[1, 1060]` for rainbow 5-term and monochromatic 4-term APs. -/
theorem good_8_5_4 : ∃ c : ℕ → Fin 8, IsGoodExactColouring 8 5 4 1060 c :=
  splitColour_isGood 4 4 353 4 (by norm_num) (by norm_num) (by norm_num) conditionI_4_353
    conditionII_4_4_353 (by norm_num) z0123 (by decide) (by intro a e he h; omega)

end Instances

end GwPower
