module

public import GwPower

public section

/-!
# Proofs of the statements in `Challenge.lean`

Each theorem below has exactly the statement of its counterpart in `Challenge.lean` (Comparator
checks this, together with the definitions the statements use, which come from `GwPower.Defs`).
The proofs are in `GwPower/Basic.lean`:

* `card_image`, `no_rainbow`, `no_mono`: parts (a), (b), (c) of Theorem 4;
* `split_card_image`, `split_no_rainbow`, `split_no_mono`: parts (a), (b), (c) of Theorem 8;
* `powerColour_isGood`, `splitColour_isGood`: relabel the colours as `Fin (m + 1)` and
  `Fin (m + s)` (`exists_good_of_card`) to obtain good exact colourings;
* `lt_of_good`: a good exact colouring of `[1, n]` puts every GW threshold above `n`;
* `good_4_4_4`, `good_5_5_4`, `good_6_6_4`, `good_6_4_4`, `good_8_5_4`: the instances, with
  conditions (i) and (ii) checked by `decide` (kernel evaluation of natural-number arithmetic).
-/

namespace GwPower

theorem theorem4 (m l p : ℕ) [Fact p.Prime] (hl : 2 ≤ l) (hlp : l < p) (hpm : p % m = 1)
    (hi : ConditionI m p) (hii : ConditionII m l p) :
    let N := (l - 1) * p
    let c := powerColour p m
    ((Finset.Icc 1 N).image c).card = m + 1 ∧
    (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + m * d ≤ N →
      ¬ ∀ i ≤ m, ∀ j ≤ m, i ≠ j → c (x + i * d) ≠ c (x + j * d)) ∧
    (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + (l - 1) * d ≤ N → ¬ ∀ j < l, c (x + j * d) = c x) :=
  ⟨card_image hl hpm, fun x d _ _ _ => no_rainbow hpm hi x d,
    fun x d hx hd hN => no_mono hl hlp hpm hii x d hx hd hN⟩

theorem exists_goodExactColouring (m l p : ℕ) [Fact p.Prime] (hl : 2 ≤ l) (hlp : l < p)
    (hpm : p % m = 1) (hi : ConditionI m p) (hii : ConditionII m l p) :
    ∃ c : ℕ → Fin (m + 1), IsGoodExactColouring (m + 1) (m + 1) l ((l - 1) * p) c :=
  powerColour_isGood m l p hl hlp hpm hi hii

theorem lt_of_gwProperty (m l p : ℕ) [Fact p.Prime] (hl : 2 ≤ l) (hlp : l < p)
    (hpm : p % m = 1) (hi : ConditionI m p) (hii : ConditionII m l p)
    (M : ℕ) (hM : GWProperty (m + 1) (m + 1) l M) : (l - 1) * p < M :=
  (powerColour_isGood m l p hl hlp hpm hi hii).elim fun _ hc => lt_of_good hc hM

theorem lt_GW (m l p : ℕ) [Fact p.Prime] (hl : 2 ≤ l) (hlp : l < p)
    (hpm : p % m = 1) (hi : ConditionI m p) (hii : ConditionII m l p)
    (hex : ∃ M, GWProperty (m + 1) (m + 1) l M) : (l - 1) * p < GW (m + 1) (m + 1) l :=
  lt_of_gwProperty m l p hl hlp hpm hi hii _ (Nat.sInf_mem hex)

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
    (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + (l - 1) * d ≤ N → ¬ ∀ j < l, c (x + j * d) = c x) :=
  ⟨split_card_image hl hpm hz, fun x d _ hd hN => split_no_rainbow hl hpm hi hzk x d hd hN,
    fun x d hx hd hN => split_no_mono hl hlp hpm hii hs hz x d hx hd hN⟩

theorem exists_goodExactColouring_split (m l p s : ℕ) [Fact p.Prime] (hl : 2 ≤ l) (hlp : l < p)
    (hpm : p % m = 1) (hi : ConditionI m p) (hii : ConditionII m l p) (hs : 2 ≤ s)
    (z : ℕ → Fin s) (hz : ∀ t : Fin s, ∃ k < l, z k = t)
    (hzk : ∀ a e : ℕ, 1 ≤ e → a + m * e < l →
      ¬ ∀ i ≤ m, ∀ j ≤ m, i ≠ j → z (a + i * e) ≠ z (a + j * e)) :
    ∃ c : ℕ → Fin (m + s), IsGoodExactColouring (m + s) (m + 1) l ((l - 1) * p + 1) c :=
  splitColour_isGood m l p s hl hlp hpm hi hii hs z hz hzk

theorem lt_of_gwProperty_split (m l p s : ℕ) [Fact p.Prime] (hl : 2 ≤ l) (hlp : l < p)
    (hpm : p % m = 1) (hi : ConditionI m p) (hii : ConditionII m l p) (hs : 2 ≤ s)
    (z : ℕ → Fin s) (hz : ∀ t : Fin s, ∃ k < l, z k = t)
    (hzk : ∀ a e : ℕ, 1 ≤ e → a + m * e < l →
      ¬ ∀ i ≤ m, ∀ j ≤ m, i ≠ j → z (a + i * e) ≠ z (a + j * e))
    (M : ℕ) (hM : GWProperty (m + s) (m + 1) l M) : (l - 1) * p + 1 < M :=
  (splitColour_isGood m l p s hl hlp hpm hi hii hs z hz hzk).elim fun _ hc => lt_of_good hc hM

theorem lt_GW_split (m l p s : ℕ) [Fact p.Prime] (hl : 2 ≤ l) (hlp : l < p)
    (hpm : p % m = 1) (hi : ConditionI m p) (hii : ConditionII m l p) (hs : 2 ≤ s)
    (z : ℕ → Fin s) (hz : ∀ t : Fin s, ∃ k < l, z k = t)
    (hzk : ∀ a e : ℕ, 1 ≤ e → a + m * e < l →
      ¬ ∀ i ≤ m, ∀ j ≤ m, i ≠ j → z (a + i * e) ≠ z (a + j * e))
    (hex : ∃ M, GWProperty (m + s) (m + 1) l M) :
    (l - 1) * p + 1 < GW (m + s) (m + 1) l :=
  lt_of_gwProperty_split m l p s hl hlp hpm hi hii hs z hz hzk _ (Nat.sInf_mem hex)

theorem gw_4_4_4 (M : ℕ) (hM : GWProperty 4 4 4 M) : 327 < M :=
  good_4_4_4.elim fun _ hc => lt_of_good hc hM

theorem gw_5_5_4 (M : ℕ) (hM : GWProperty 5 5 4 M) : 1059 < M :=
  good_5_5_4.elim fun _ hc => lt_of_good hc hM

theorem gw_6_6_4 (M : ℕ) (hM : GWProperty 6 6 4 M) : 2253 < M :=
  good_6_6_4.elim fun _ hc => lt_of_good hc hM

theorem gw_6_4_4 (M : ℕ) (hM : GWProperty 6 4 4 M) : 328 < M :=
  good_6_4_4.elim fun _ hc => lt_of_good hc hM

theorem gw_8_5_4 (M : ℕ) (hM : GWProperty 8 5 4 M) : 1060 < M :=
  good_8_5_4.elim fun _ hc => lt_of_good hc hM

end GwPower
