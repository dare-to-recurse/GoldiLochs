module

public import GoldiLochs.Remainders
public import GoldiLochs.Scale
import Mathlib.Tactic

/-! # An additive Euclidean cost that vanishes on quotient-one steps -/

@[expose] public section

open Filter
open scoped BigOperators Topology

namespace GoldiLochs

/-- The positive linear form scaled by the golden ratio on quotient-one steps. -/
noncomputable def goldenHeight (a b : ℕ) : ℝ := a + (phi - 1) * b

private theorem one_lt_phi : 1 < phi := by linarith [phi_gt_three_halves]

private theorem log_phi_pos : 0 < Real.log phi := Real.log_pos one_lt_phi

private theorem goldenHeight_pos {a : ℕ} (ha : 0 < a) (b : ℕ) :
    0 < goldenHeight a b := by
  unfold goldenHeight
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  exact add_pos_of_pos_of_nonneg ha'
    (mul_nonneg (sub_nonneg.mpr one_lt_phi.le) (Nat.cast_nonneg b))

theorem goldenHeight_step (a b : ℕ) :
    goldenHeight a b = phi * goldenHeight b (a % b) + ((a / b : ℕ) - (1 : ℝ)) * b := by
  have hmod := Nat.mod_add_div a b
  have hcast : (a % b : ℕ) + (b : ℝ) * (a / b : ℕ) = (a : ℝ) := by
    exact_mod_cast hmod
  have hphi : phi * (phi - 1) = 1 := by nlinarith [phi_sq]
  unfold goldenHeight
  calc
    _ = (a % b : ℕ) + (b : ℝ) * (a / b : ℕ) + (phi - 1) * b := by rw [hcast]
    _ = _ := by linear_combination -((a % b : ℕ) : ℝ) * hphi

/-- Log growth in excess of the quotient-one factor at one Euclidean step. -/
noncomputable def goldenStepCost (a b : ℕ) : ℝ :=
  Real.log (goldenHeight a b / (phi * goldenHeight b (a % b)))

theorem goldenStepCost_eq_log (a : ℕ) {b : ℕ} (hb : 0 < b) :
    goldenStepCost a b =
      Real.log (1 + ((a / b : ℕ) - (1 : ℝ)) * b / (phi * goldenHeight b (a % b))) := by
  have h : phi * goldenHeight b (a % b) ≠ 0 :=
    (mul_pos (zero_lt_one.trans one_lt_phi) (goldenHeight_pos hb _)).ne'
  unfold goldenStepCost
  congr 1
  conv_lhs => rw [goldenHeight_step a b, add_div, div_self h]

theorem goldenStepCost_nonneg {a b : ℕ} (hba : b ≤ a) (hb : 0 < b) :
    0 ≤ goldenStepCost a b := by
  rw [goldenStepCost_eq_log a hb]
  apply Real.log_nonneg
  have hquot : (1 : ℝ) ≤ (a / b : ℕ) := by exact_mod_cast Nat.div_pos hba hb
  have hheight : 0 ≤ phi * goldenHeight b (a % b) :=
    (mul_pos (zero_lt_one.trans one_lt_phi) (goldenHeight_pos hb _)).le
  exact le_add_of_nonneg_right
    (div_nonneg (mul_nonneg (sub_nonneg.mpr hquot) (Nat.cast_nonneg b)) hheight)

theorem goldenStepCost_eq_zero {a b : ℕ} (hb : 0 < b) (hquot : a / b = 1) :
    goldenStepCost a b = 0 := by
  rw [goldenStepCost_eq_log a hb, hquot]
  simp

/-- The current quotient alone bounds the step cost from either side. -/
theorem goldenStepCost_quotient_bounds {a b : ℕ} (hba : b ≤ a) (hb : 0 < b) :
    Real.log (1 + ((a / b : ℕ) - (1 : ℝ)) / phi ^ 2) ≤ goldenStepCost a b ∧
      goldenStepCost a b ≤ Real.log (1 + ((a / b : ℕ) - (1 : ℝ)) / phi) := by
  let e : ℝ := (a / b : ℕ) - (1 : ℝ)
  let d := phi * goldenHeight b (a % b) / (b : ℝ)
  have hp : 0 < phi := zero_lt_one.trans one_lt_phi
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hr : ((a % b : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast (Nat.mod_lt a hb).le
  have he : 0 ≤ e := by
    change 0 ≤ ((a / b : ℕ) : ℝ) - 1
    exact sub_nonneg.mpr (by exact_mod_cast Nat.div_pos hba hb)
  have hd : 0 < d := div_pos (mul_pos hp (goldenHeight_pos hb _)) hb'
  have hheight : (b : ℝ) ≤ goldenHeight b (a % b) ∧
      goldenHeight b (a % b) ≤ phi * (b : ℝ) := by
    unfold goldenHeight
    have h := sub_nonneg.mpr one_lt_phi.le
    constructor
    · exact le_add_of_nonneg_right (mul_nonneg h (Nat.cast_nonneg _))
    · linarith [mul_le_mul_of_nonneg_left hr h]
  have hdlo : phi ≤ d :=
    (le_div_iff₀ hb').mpr (mul_le_mul_of_nonneg_left hheight.1 hp.le)
  have hdhi : d ≤ phi ^ 2 := by
    apply (div_le_iff₀ hb').mpr
    simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_left hheight.2 hp.le
  have heq : goldenStepCost a b = Real.log (1 + e / d) := by
    rw [goldenStepCost_eq_log a hb]
    congr 1
    change 1 + e * (b : ℝ) / (phi * goldenHeight b (a % b)) = 1 + e / d
    rw [show d = phi * goldenHeight b (a % b) / (b : ℝ) from rfl, div_div_eq_mul_div]
  rw [heq]
  change Real.log (1 + e / phi ^ 2) ≤ Real.log (1 + e / d) ∧
    Real.log (1 + e / d) ≤ Real.log (1 + e / phi)
  exact ⟨Real.log_le_log (by positivity)
    (add_le_add_right (div_le_div_of_nonneg_left he hd hdhi) 1),
    Real.log_le_log (by positivity) (add_le_add_right (div_le_div_of_nonneg_left he hp hdlo) 1)⟩

/-- Total excess logarithmic growth along a finite Euclidean orbit. -/
noncomputable def euclidGoldenCost (a b : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (euclidDepth a b),
    goldenStepCost (euclidRemainder a b i) (euclidRemainder a b (i + 1))

private theorem euclidGoldenCost_step (a : ℕ) {b : ℕ} (hb : 0 < b) :
    euclidGoldenCost a b = goldenStepCost a b + euclidGoldenCost b (a % b) := by
  simp only [euclidGoldenCost, euclidDepth_step a hb, Nat.add_comm 1,
    Finset.sum_range_succ', Nat.zero_add, euclidRemainder_zero, euclidRemainder_one]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [euclidRemainder_step a hb i, euclidRemainder_step a hb (i + 1)]

theorem euclidGoldenCost_nonneg {a b : ℕ} (hba : b ≤ a) : 0 ≤ euclidGoldenCost a b := by
  by_cases hb : b = 0
  · simp [hb, euclidGoldenCost]
  · have hb' := Nat.pos_of_ne_zero hb
    rw [euclidGoldenCost_step a hb']
    exact add_nonneg (goldenStepCost_nonneg hba hb')
      (euclidGoldenCost_nonneg (Nat.mod_lt a hb').le)
termination_by b
decreasing_by exact Nat.mod_lt _ hb'

theorem euclidGoldenCost_identity {a : ℕ} (ha : 0 < a) (b : ℕ) :
    euclidGoldenCost a b + Real.log (a.gcd b : ℝ) +
      (euclidDepth a b : ℝ) * Real.log phi = Real.log (goldenHeight a b) := by
  by_cases hb : b = 0
  · simp [hb, euclidGoldenCost, goldenHeight]
  · have hb' := Nat.pos_of_ne_zero hb
    have hind := euclidGoldenCost_identity hb' (a % b)
    have hprev := goldenHeight_pos ha b
    have hnext := goldenHeight_pos hb' (a % b)
    have hp := zero_lt_one.trans one_lt_phi
    rw [euclidGoldenCost_step a hb', ← gcd_mod_step a b,
      euclidDepth_step a hb', Nat.cast_add, Nat.cast_one, goldenStepCost,
      Real.log_div hprev.ne' (mul_pos hp hnext).ne', Real.log_mul hp.ne' hnext.ne']
    linarith
termination_by b
decreasing_by exact Nat.mod_lt _ hb'

/-- The part of the initial decimal log height not accounted for by `depth * log phi`. -/
noncomputable def decimalGoldenCost (n : ℕ) : ℝ :=
  Real.log (commonFactor n : ℝ) + euclidGoldenCost (residualU n) (residualV n)

theorem decimalGoldenCost_nonneg {n : ℕ} (hn : 1 ≤ n) : 0 ≤ decimalGoldenCost n := by
  have hUV := residual_twice_le hn
  have hg : (1 : ℝ) ≤ (commonFactor n : ℝ) := by exact_mod_cast commonFactor_pos n
  exact add_nonneg (Real.log_nonneg hg) (euclidGoldenCost_nonneg (by omega))

theorem decimalGoldenCost_identity {n : ℕ} (hn : 1 ≤ n) :
    decimalGoldenCost n + (depth n : ℝ) * Real.log phi =
      Real.log (Real.sqrt 5 * (decimalDenominator n : ℝ) - delta n) := by
  let s := decimalSplit n
  let u := residualU n
  let v := residualV n
  let d := commonFactor n
  have hU := residual_twice_le hn
  have hV := residualV_pos hn
  have hU' : 0 < u := by change 0 < residualU n; omega
  have hscalar : 0 < (d : ℝ) := by exact_mod_cast commonFactor_pos n
  obtain ⟨hUscale, hVscale⟩ := residual_exact hn
  have hheight : goldenHeight s.u s.v = (d : ℝ) * goldenHeight u v := by
    change goldenHeight (decimalSplit n).u (decimalSplit n).v = _
    rw [← hUscale, ← hVscale]
    simp only [goldenHeight, Nat.cast_mul]
    ring
  have hform := (stripOnes_linear (truncationNumeratorExact n) (decimalDenominator n)).1
  change phi ^ s.count * goldenHeight s.u s.v =
    (truncationNumeratorExact n : ℝ) + (phi - 1) * decimalDenominator n at hform
  rw [← truncationNumerator_eq_exact, hheight] at hform
  have hinput : (truncationNumerator n : ℝ) + (phi - 1) * decimalDenominator n =
      Real.sqrt 5 * (decimalDenominator n : ℝ) - delta n := by
    unfold delta phi
    ring
  rw [← hinput, ← hform, Real.log_mul (pow_pos (zero_lt_one.trans one_lt_phi) _).ne'
    (mul_pos hscalar (goldenHeight_pos hU' _)).ne',
    Real.log_mul hscalar.ne' (goldenHeight_pos hU' _).ne', Real.log_pow]
  have hind := euclidGoldenCost_identity hU' v
  have hcop : u.gcd v = 1 := (residual_coprime hn).gcd_eq_one
  rw [hcop, Nat.cast_one, Real.log_one, add_zero] at hind
  rw [depth_eq_prefix_add_tail hn, Nat.cast_add]
  change Real.log (d : ℝ) + euclidGoldenCost u v +
      ((s.count : ℝ) + (euclidDepth u v : ℝ)) * Real.log phi = _
  linarith

private theorem initialHeight_scale :
    Tendsto (fun n : ℕ => Real.log (Real.sqrt 5 * (decimalDenominator n : ℝ) - delta n) /
      (n : ℝ)) atTop (𝓝 (Real.log 10)) := by
  have hconst := tendsto_const_nhds (x := Real.log 10) (f := atTop (α := ℕ))
  have hupper := hconst.add (tendsto_const_div_atTop_nhds_zero_nat (Real.log 3))
  rw [add_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hconst hupper
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hq : 0 < (decimalDenominator n : ℝ) := by exact_mod_cast decimalDenominator_pos n
    have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hlog := Real.log_le_log hq (delta_factor_bounds n).1.le
    rw [log_decimalDenominator] at hlog
    exact (le_div_iff₀ hn').2 (by linarith)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hq : 0 < (decimalDenominator n : ℝ) := by exact_mod_cast decimalDenominator_pos n
    have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hlog := Real.log_le_log (hq.trans (delta_factor_bounds n).1)
      (delta_factor_bounds n).2.le
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hq.ne', log_decimalDenominator] at hlog
    change _ ≤ Real.log 10 + Real.log 3 / (n : ℝ)
    apply (div_le_iff₀ hn').2
    rw [add_mul, div_mul_cancel₀ _ hn'.ne']
    linarith

/-- The exact depth limit is equivalent to one limit for the total non-one cost
of the actual reduced tail plus the logarithm of the common factor. -/
theorem target_iff_decimalGoldenCost :
    Target ↔ Tendsto (fun n : ℕ => decimalGoldenCost n / (n : ℝ))
      atTop (𝓝 (Real.log 10 - proposedConstant * Real.log phi)) := by
  have hrel : ∀ᶠ n : ℕ in atTop,
      decimalGoldenCost n / (n : ℝ) + ((depth n : ℝ) / (n : ℝ)) * Real.log phi =
        Real.log (Real.sqrt 5 * (decimalDenominator n : ℝ) - delta n) / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [div_mul_eq_mul_div, ← add_div, decimalGoldenCost_identity hn]
  unfold Target
  constructor
  · intro h
    have ht := initialHeight_scale.sub (h.mul_const (Real.log phi))
    apply ht.congr'
    filter_upwards [hrel] with n hn
    exact sub_eq_of_eq_add hn.symm
  · intro h
    have ht := (initialHeight_scale.sub h).div_const (Real.log phi)
    rw [sub_sub_cancel, mul_div_cancel_right₀ _ log_phi_pos.ne'] at ht
    apply ht.congr'
    filter_upwards [hrel] with n hn
    exact (div_eq_iff log_phi_pos.ne').2 (sub_eq_of_eq_add (by rw [← hn, add_comm]))

end GoldiLochs
