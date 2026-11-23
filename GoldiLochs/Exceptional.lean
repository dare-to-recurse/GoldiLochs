/-
Copyright (c) 2026 Daniel Karlsson. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Daniel Karlsson
-/
module

public import GoldiLochs.Scale
public import GoldiLochs.Tail
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! # Exceptional normalized lengths before dropping the prefix -/

public section

open Filter

namespace GoldiLochs

private theorem log_phi_lt_half : Real.log phi < 1 / 2 := by
  have hsqrt : Real.sqrt 5 < (56 : ℝ) / 25 := by
    apply (Real.sqrt_lt (by norm_num) (by norm_num)).2
    norm_num
  have hphi : phi < (81 : ℝ) / 50 := by unfold phi; linarith
  have hstep : (17 : ℝ) / 16 ≤ Real.exp (1 / 16) := by
    linarith [Real.add_one_le_exp ((1 : ℝ) / 16)]
  have hpow : ((17 : ℝ) / 16) ^ 8 ≤ Real.exp (1 / 16) ^ 8 := by gcongr
  have hexp : Real.exp ((1 : ℝ) / 2) = Real.exp (1 / 16) ^ 8 := by
    rw [← Real.exp_natCast_mul]
    norm_num
  have hphiExp : phi < Real.exp (1 / 2) := by
    rw [hexp]
    exact hphi.trans_le ((by norm_num : (81 : ℝ) / 50 ≤ (17 / 16) ^ 8).trans hpow)
  have hpos : 0 < phi := by linarith [phi_gt_three_halves]
  rwa [← Real.log_lt_log_iff hpos (Real.exp_pos _), Real.log_exp] at hphiExp

theorem euclideanRate_lt_prefix_per_log :
    euclideanRate < 1 / (2 * Real.log phi) := by
  have hphi : 0 < Real.log phi := by apply Real.log_pos; linarith [phi_gt_three_halves]
  have hlog2 : Real.log 2 < 3 / 4 := by linarith [Real.log_two_lt_d9]
  have hm1 := mul_lt_mul_of_pos_right hlog2 hphi
  have hm2 := mul_lt_mul_of_pos_left log_phi_lt_half (by norm_num : (0 : ℝ) < 3 / 4)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpisq : (9 : ℝ) < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]
  rw [euclideanRate]
  apply (div_lt_div_iff₀ (sq_pos_of_pos hpi) (by positivity)).2
  nlinarith

private theorem reduced_decimal_denominator_gt_one {n : ℕ} (hn : 1 ≤ n) :
    1 < decimalDenominator n / commonFactor n := by
  have hd : commonFactor n ∣ decimalDenominator n := Nat.gcd_dvd_right _ _
  have ha : commonFactor n ∣ truncationNumerator n := by
    rw [truncationNumerator_eq_exact]
    exact Nat.gcd_dvd_left _ _
  have hcancel := Nat.div_mul_cancel hd
  have hq := decimalDenominator_pos n
  by_contra h
  have heq : decimalDenominator n / commonFactor n = 1 := by
    have hne : decimalDenominator n / commonFactor n ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hcancel
      omega
    exact (Nat.le_of_not_gt h).antisymm (Nat.one_le_iff_ne_zero.mpr hne)
  rw [heq, one_mul] at hcancel
  rw [hcancel] at ha
  obtain ⟨m, hm⟩ := ha
  have hlo := denominator_lt_numerator hn
  have hhi : truncationNumerator n < 2 * decimalDenominator n := by
    have hphi : phi < 2 := by
      have hs : Real.sqrt 5 < 3 := (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
      unfold phi
      linarith
    have hqReal : 0 < (decimalDenominator n : ℝ) := by exact_mod_cast hq
    have hdelta : 0 < phi * (decimalDenominator n : ℝ) - (truncationNumerator n : ℝ) :=
      delta_pos n
    exact_mod_cast (show (truncationNumerator n : ℝ) < 2 * (decimalDenominator n : ℝ)
      by linarith [mul_lt_mul_of_pos_right hphi hqReal])
  rw [hm] at hlo hhi
  have hm2 : 2 ≤ m := by
    by_contra! hlt
    have : decimalDenominator n * m ≤ decimalDenominator n * 1 :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have := Nat.mul_le_mul_left (decimalDenominator n) hm2
  omega

private theorem prefix_count_lower {n : ℕ} (hn : 1 ≤ n) :
    Real.log (decimalDenominator n : ℝ) / 2 - (Real.log 2 + Real.log 12 / 2) ≤
      ((decimalSplit n).count : ℝ) * Real.log phi := by
  have hlog : Real.log (delta n) ≤ 0 := by
    exact Real.log_nonpos (delta_pos n).le (delta_lt_one n).le
  linarith [(split_height_log_bounds hn).2, (split_prefix_log_bounds hn).1]

/-- The original decimal numerator, with its integer part removed, has
normalized continued-fraction length above the ensemble constant by a fixed
positive margin. The lower bound uses the prefix and the uniform finite scale
estimates directly. -/
theorem original_length_eventually_exceptional :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ n in atTop, euclideanRate + ε <
        ((depth n : ℝ) - 1) / Real.log ((decimalDenominator n / commonFactor n : ℕ) : ℝ) := by
  let ε : ℝ := (1 / (2 * Real.log phi) - euclideanRate) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith [euclideanRate_lt_prefix_per_log]
  have hrate : 0 < euclideanRate := by unfold euclideanRate; positivity
  have hlogPhi : 0 < Real.log phi := by apply Real.log_pos; linarith [phi_gt_three_halves]
  have hlog10 : 0 < Real.log 10 := by positivity
  let D : ℝ := Real.log 2 + Real.log 12 / 2
  obtain ⟨N, hN⟩ := exists_nat_gt (D / (ε * Real.log 10 * Real.log phi))
  have hfactor : 0 < ε * Real.log 10 * Real.log phi := by positivity
  have hN' := (div_lt_iff₀ hfactor).mp hN
  refine ⟨ε, hε, ?_⟩
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop N] with n hn hnN
  have hqgt := reduced_decimal_denominator_gt_one hn
  have hlogq : 0 < Real.log ((decimalDenominator n / commonFactor n : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hqgt
  have hqle : (decimalDenominator n / commonFactor n : ℕ) ≤ decimalDenominator n :=
    Nat.div_le_self _ _
  have hlogqle : Real.log ((decimalDenominator n / commonFactor n : ℕ) : ℝ) ≤
      Real.log (decimalDenominator n : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast (lt_trans Nat.zero_lt_one hqgt)
    · exact_mod_cast hqle
  have hD : D < ε * Real.log (decimalDenominator n : ℝ) * Real.log phi := by
    rw [log_decimalDenominator]
    have hcast : (N : ℝ) ≤ n := by exact_mod_cast hnN
    have hmul := mul_le_mul_of_nonneg_right hcast hfactor.le
    calc
      D < (N : ℝ) * (ε * Real.log 10 * Real.log phi) := hN'
      _ ≤ (n : ℝ) * (ε * Real.log 10 * Real.log phi) := hmul
      _ = _ := by ring
  have hrateEq : (euclideanRate + ε) * Real.log phi = 1 / 2 - ε * Real.log phi := by
    dsimp [ε]
    field_simp [hlogPhi.ne']
    ring
  have hprefix : (euclideanRate + ε) * Real.log (decimalDenominator n : ℝ) <
      ((decimalSplit n).count : ℝ) := by
    apply lt_of_mul_lt_mul_right (a := Real.log phi) ?_ hlogPhi.le
    rw [mul_right_comm, hrateEq]
    have hlower := prefix_count_lower hn
    change Real.log (decimalDenominator n : ℝ) / 2 - D ≤ _ at hlower
    nlinarith [hD, hlower]
  have htailPos : 1 ≤ tailDepth n := by
    rw [tailDepth, euclidDepth_step _ (residualV_pos hn)]
    omega
  have hdepth : ((decimalSplit n).count : ℝ) ≤ (depth n : ℝ) - 1 := by
    rw [depth_eq_prefix_add_tail hn, Nat.cast_add]
    have : (1 : ℝ) ≤ (tailDepth n : ℝ) := by exact_mod_cast htailPos
    linarith
  apply (lt_div_iff₀ hlogq).2
  exact (mul_le_mul_of_nonneg_left hlogqle (by positivity)).trans_lt (hprefix.trans_le hdepth)

end GoldiLochs
