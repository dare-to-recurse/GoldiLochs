module

public import GoldiLochs.Split
import Mathlib.Tactic

/-! # Backward rational approximation at the final Euclidean quotient -/

@[expose] public section

namespace GoldiLochs

/-- The final quotient of the complete Euclidean expansion. -/
def lastEuclideanQuotient (a b : ℕ) : ℕ :=
  if _hb : b = 0 then 0 else
    if a % b = 0 then a / b else lastEuclideanQuotient b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero _hb)

/-- The rational obtained by deleting the final quotient of the expansion of `b/a`.
The first quotient of `a/b` acts by the map `x ↦ 1/(q+x)` on the shorter expansion. -/
def penultimatePair (a b : ℕ) : ℕ × ℕ :=
  if _hb : b = 0 then (0, 1) else
    if a % b = 0 then (0, 1) else
      let (p, s) := penultimatePair b (a % b)
      (s, (a / b) * s + p)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero _hb)

theorem penultimatePair_spec {a b : ℕ} (hb : 0 < b) (hab : b < a) (hcop : a.Coprime b) :
    let t := lastEuclideanQuotient a b
    let (p, s) := penultimatePair a b
    2 ≤ t ∧ 0 < s ∧ p ≤ s ∧ t * p ≤ b ∧ t * s ≤ a ∧
      (b : ℤ) * s - (a : ℤ) * p = (-1) ^ (euclidDepth a b - 1) := by
  have hb0 : b ≠ 0 := hb.ne'
  rw [lastEuclideanQuotient, penultimatePair, dite_eq_right hb0, dite_eq_right hb0]
  by_cases hr : a % b = 0
  · rw [ite_eq_left hr, ite_eq_left hr, euclidDepth_step a hb, hr, euclidDepth_zero]
    have hbb : b = 1 := by
      have hg := gcd_mod_step a b
      rw [hr, Nat.gcd_zero_right, hcop.gcd_eq_one] at hg
      exact hg
    subst b
    simp_all
    omega
  · rw [ite_eq_right hr, ite_eq_right hr, euclidDepth_step a hb]
    have hrec : 0 < a % b := Nat.pos_of_ne_zero hr
    have hrb : a % b < b := Nat.mod_lt a hb
    have hrec_cop : b.Coprime (a % b) := (gcd_mod_step a b).trans hcop.gcd_eq_one
    have ih := penultimatePair_spec hrec hrb hrec_cop
    rcases hpair : penultimatePair b (a % b) with ⟨p, s⟩
    rw [hpair] at ih
    dsimp only at ih
    obtain ⟨ht, hs, hps, htp, hts, hdet⟩ := ih
    let t := lastEuclideanQuotient b (a % b)
    change 2 ≤ t ∧ 0 < (a / b) * s + p ∧ s ≤ (a / b) * s + p ∧
      t * s ≤ b ∧ t * ((a / b) * s + p) ≤ a ∧ _
    have hq : 0 < a / b := Nat.div_pos hab.le hb
    have hsle : s ≤ (a / b) * s := by
      simpa using Nat.mul_le_mul_right s (show 1 ≤ a / b by omega)
    refine ⟨ht, by omega, by omega, hts, ?_, ?_⟩
    · calc
        t * ((a / b) * s + p) = a / b * (t * s) + t * p := by ring
        _ ≤ a / b * b + a % b := Nat.add_le_add (Nat.mul_le_mul_left _ hts) htp
        _ = a := by simpa [Nat.add_comm] using Nat.mod_add_div' a b
    have hdepth : 0 < euclidDepth b (a % b) := by rw [euclidDepth_step b hrec]; omega
    have hsub : 1 + euclidDepth b (a % b) - 1 = (euclidDepth b (a % b) - 1) + 1 := by omega
    rw [hsub, pow_succ, ← hdet]
    push_cast
    have hdiv : (a % b : ℤ) + (a / b : ℤ) * (b : ℤ) = a := by
      exact_mod_cast Nat.mod_add_div' a b
    linear_combination (s : ℤ) * hdiv
termination_by b

theorem penultimatePair_coprime {a b : ℕ} (hb : 0 < b) (hab : b < a) (hcop : a.Coprime b) :
    let (p, s) := penultimatePair a b
    p.Coprime s := by
  have h := penultimatePair_spec hb hab hcop
  rcases hpairs : penultimatePair a b with ⟨p, s⟩
  rw [hpairs] at h
  rcases h with ⟨_, _, _, _, _, hdet⟩
  change p.gcd s = 1
  apply Nat.dvd_one.mp
  apply Int.natCast_dvd_natCast.mp
  have hp : (p.gcd s : ℤ) ∣ (p : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left p s)
  have hs : (p.gcd s : ℤ) ∣ (s : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right p s)
  have hd : (p.gcd s : ℤ) ∣ (-1 : ℤ) ^ (euclidDepth a b - 1) := by
    rw [← hdet]
    exact dvd_sub (dvd_mul_of_dvd_right hs _) (dvd_mul_of_dvd_right hp _)
  exact dvd_trans hd (isUnit_iff_dvd_one.mp (isUnit_neg_one.pow _))

theorem penultimatePair_error {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a b : ℕ} (hb : 0 < b) (hab : b < a) (hcop : a.Coprime b) :
    let (p, s) := penultimatePair a b
    |(b : K) / a - (p : K) / s| = 1 / ((a : K) * s) := by
  have h := penultimatePair_spec hb hab hcop
  rcases hpairs : penultimatePair a b with ⟨p, s⟩
  rw [hpairs] at h
  dsimp only at h ⊢
  rcases h with ⟨_, hs, _, _, _, hdet⟩
  have ha : 0 < (a : K) := by exact_mod_cast (hb.trans hab)
  have hs' : 0 < (s : K) := by exact_mod_cast hs
  have hdet' : (b : K) * s - (a : K) * p = (-1 : K) ^ (euclidDepth a b - 1) := by
    exact_mod_cast hdet
  have herr : (b : K) / a - (p : K) / s =
      ((b : K) * s - (a : K) * p) / ((a : K) * s) := by
    field_simp
  rw [herr, abs_div, hdet', abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (mul_pos ha hs')]

theorem residualPenultimatePair_spec {n : ℕ} (hn : 1 ≤ n) :
    let t := lastEuclideanQuotient (residualU n) (residualV n)
    let (p, s) := penultimatePair (residualU n) (residualV n)
    2 ≤ t ∧ 0 < s ∧ p ≤ s ∧ p.Coprime s ∧ t * s ≤ residualU n ∧
      |(residualV n : ℝ) / residualU n - (p : ℝ) / s| =
        1 / ((residualU n : ℝ) * s) := by
  have hpos := residualV_pos hn
  have htwice := residual_twice_le hn
  have hlt : residualV n < residualU n := by omega
  have hcop := residual_coprime hn
  have hspec := penultimatePair_spec hpos hlt hcop
  have hc := penultimatePair_coprime hpos hlt hcop
  have he := penultimatePair_error (K := ℝ) hpos hlt hcop
  rcases hpairs : penultimatePair (residualU n) (residualV n) with ⟨p, s⟩
  rw [hpairs] at hspec hc he
  rcases hspec with ⟨ht, hs, hps, _, hts, _⟩
  exact ⟨ht, hs, hps, hc, hts, he⟩

/-- For a residual tail with at least two quotients the penultimate approximation
has positive numerator strictly smaller than its denominator. -/
theorem residualPenultimatePair_proper {n : ℕ} (hn : 1 ≤ n) (hdepth : 1 < tailDepth n) :
    let (p, s) := penultimatePair (residualU n) (residualV n)
    0 < p ∧ p < s := by
  let a := residualU n
  let b := residualV n
  have hb : 0 < b := residualV_pos hn
  have hab : 2 * b ≤ a := residual_twice_le hn
  have hcop : a.Coprime b := residual_coprime hn
  have hr : a % b ≠ 0 := by
    intro h
    change 1 < euclidDepth a b at hdepth
    rw [euclidDepth_step a hb, h, euclidDepth_zero] at hdepth
    omega
  have hs := penultimatePair_spec (Nat.pos_of_ne_zero hr) (Nat.mod_lt a hb)
    ((gcd_mod_step a b).trans hcop.gcd_eq_one)
  change let (p, s) := penultimatePair a b; 0 < p ∧ p < s
  rw [penultimatePair, dite_eq_right hb.ne', ite_eq_right hr]
  rcases hpair : penultimatePair b (a % b) with ⟨p, s⟩
  rw [hpair] at hs
  rcases hs with ⟨_, hs, _, _, _, _⟩
  have hq : 2 ≤ a / b := (Nat.le_div_iff_mul_le hb).2 hab
  have hqmul : 2 * s ≤ (a / b) * s := Nat.mul_le_mul_right s hq
  exact ⟨hs, by omega⟩

/-- An approximation lower bound weighted by the fourth power of the penultimate
denominator gives an upper bound on the cube of the final quotient. -/
theorem residualLastEuclideanQuotient_weighted_error_le {n : ℕ} (hn : 1 ≤ n) :
    let t := lastEuclideanQuotient (residualU n) (residualV n)
    let (p, s) := penultimatePair (residualU n) (residualV n)
    (t : ℝ) ^ 3 *
      ((s : ℝ) ^ 4 * |(residualV n : ℝ) / residualU n - (p : ℝ) / s|) ≤
        (residualU n : ℝ) ^ 2 := by
  have h := residualPenultimatePair_spec hn
  rcases hpairs : penultimatePair (residualU n) (residualV n) with ⟨p, s⟩
  rw [hpairs] at h
  dsimp only at h ⊢
  rcases h with ⟨_, hs, _, _, hts, he⟩
  let t := lastEuclideanQuotient (residualU n) (residualV n)
  let U : ℝ := residualU n
  change (t : ℝ) ^ 3 * ((s : ℝ) ^ 4 * _) ≤ U ^ 2
  have hts' : (t : ℝ) * s ≤ U := by
    dsimp [t, U]
    exact_mod_cast hts
  have hs' : 0 < (s : ℝ) := by exact_mod_cast hs
  have hU : 0 < U := by
    have hv := residualV_pos hn
    have htwice := residual_twice_le hn
    dsimp [U]
    exact_mod_cast (show 0 < residualU n by omega)
  rw [he]
  calc
    (t : ℝ) ^ 3 * ((s : ℝ) ^ 4 * (1 / (U * s))) =
        ((t : ℝ) * s) ^ 3 / U := by
      field_simp
    _ ≤ U ^ 3 / U := div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hts' _) hU.le
    _ = U ^ 2 := by field_simp

end GoldiLochs
