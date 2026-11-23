module

public import GoldiLochs.Split
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # Uniform error bounds and the Diophantine input for the two scales -/

public section

open Filter
open scoped Topology

namespace GoldiLochs

private theorem cast_denominator_pos (n : ℕ) : 0 < (decimalDenominator n : ℝ) :=
  by exact_mod_cast decimalDenominator_pos n

private theorem cast_split_u_pos {n : ℕ} (hn : 1 ≤ n) : 0 < ((decimalSplit n).u : ℝ) := by
  obtain ⟨hv, hu, _, _⟩ := decimalSplit_spec hn
  exact_mod_cast (show 0 < (decimalSplit n).u by omega)

theorem log_decimalDenominator (n : ℕ) :
    Real.log (decimalDenominator n : ℝ) = (n : ℝ) * Real.log 10 := by
  rw [decimalDenominator, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

theorem split_height_sq_bounds {n : ℕ} (hn : 1 ≤ n) :
    (decimalDenominator n : ℝ) * delta n < ((decimalSplit n).u : ℝ) ^ 2 ∧
      ((decimalSplit n).u : ℝ) ^ 2 < 12 * ((decimalDenominator n : ℝ) * delta n) := by
  obtain ⟨hv, hu, _, _⟩ := decimalSplit_spec hn
  have h := quadraticForm_bounds (u := ((decimalSplit n).u : ℝ))
    (v := ((decimalSplit n).v : ℝ)) (by exact_mod_cast hv) (by exact_mod_cast hu)
  rw [decimalSplit_form hn] at h
  obtain ⟨hlo, hhi⟩ := delta_factor_bounds n
  constructor
  · linarith [mul_lt_mul_of_pos_left hlo (delta_pos n)]
  · linarith [mul_lt_mul_of_pos_left hhi (delta_pos n)]

theorem split_height_log_bounds {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ 2 * Real.log ((decimalSplit n).u : ℝ) -
        (Real.log (decimalDenominator n : ℝ) + Real.log (delta n)) ∧
      2 * Real.log ((decimalSplit n).u : ℝ) -
        (Real.log (decimalDenominator n : ℝ) + Real.log (delta n)) ≤ Real.log 12 := by
  have hq := cast_denominator_pos n
  have hd := delta_pos n
  obtain ⟨hlo, hhi⟩ := split_height_sq_bounds hn
  have hloglo := Real.log_le_log (mul_pos hq hd) hlo.le
  have hloghi := Real.log_le_log (pow_pos (cast_split_u_pos hn) 2) hhi.le
  rw [Real.log_mul hq.ne' hd.ne', Real.log_pow] at hloglo
  rw [Real.log_mul (by norm_num : (12 : ℝ) ≠ 0) (mul_pos hq hd).ne',
    Real.log_mul hq.ne' hd.ne', Real.log_pow] at hloghi
  norm_num at hloglo hloghi
  constructor <;> linarith

theorem split_prefix_log_bounds {n : ℕ} (hn : 1 ≤ n) :
    -Real.log 2 ≤ (decimalSplit n).count * Real.log phi +
        Real.log ((decimalSplit n).u : ℝ) - Real.log (decimalDenominator n : ℝ) ∧
      (decimalSplit n).count * Real.log phi +
        Real.log ((decimalSplit n).u : ℝ) - Real.log (decimalDenominator n : ℝ) ≤ Real.log 3 := by
  let s := decimalSplit n
  let q : ℝ := decimalDenominator n
  let a : ℝ := truncationNumerator n
  let w : ℝ := (s.u : ℝ) + (phi - 1) * (s.v : ℝ)
  have hq : 0 < q := cast_denominator_pos n
  have hu : 0 < (s.u : ℝ) := cast_split_u_pos hn
  have hp : 0 < phi := by linarith [phi_gt_three_halves]
  have hphi2 : phi < 2 := by
    have h : Real.sqrt 5 < (3 : ℝ) := (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
    unfold phi
    linarith
  have hv : (0 : ℝ) ≤ (s.v : ℝ) := Nat.cast_nonneg _
  have hsv : 2 * (s.v : ℝ) ≤ (s.u : ℝ) := by
    exact_mod_cast (decimalSplit_spec hn).2.1
  have hwlo : (s.u : ℝ) ≤ w := le_add_of_nonneg_right (mul_nonneg (by
    linarith [phi_gt_three_halves]) hv)
  have hwhi : w ≤ 2 * (s.u : ℝ) := by
    dsimp [w]
    nlinarith [mul_le_mul_of_nonneg_right hphi2.le hv]
  have hlinear := (stripOnes_linear (truncationNumeratorExact n) (decimalDenominator n)).1
  change phi ^ s.count * w = (truncationNumeratorExact n : ℝ) + (phi - 1) * q at hlinear
  rw [← truncationNumerator_eq_exact] at hlinear
  change phi ^ s.count * w = a + (phi - 1) * q at hlinear
  have haq : q ≤ a := by
    change (decimalDenominator n : ℝ) ≤ (truncationNumerator n : ℝ)
    exact_mod_cast (denominator_lt_numerator hn).le
  have hδ : 0 < phi * q - a := delta_pos n
  have hlinlo : q ≤ phi ^ s.count * w := by
    rw [hlinear]
    linarith [mul_nonneg (show 0 ≤ phi - 1 by linarith [phi_gt_three_halves]) hq.le]
  have hlinhi : phi ^ s.count * w ≤ 3 * q := by
    rw [hlinear]
    linarith [mul_lt_mul_of_pos_right hphi2 hq]
  have hpow := pow_pos hp s.count
  have hlo : q ≤ 2 * (phi ^ s.count * (s.u : ℝ)) := by
    linarith [hlinlo, mul_le_mul_of_nonneg_left hwhi hpow.le]
  have hhi : phi ^ s.count * (s.u : ℝ) ≤ 3 * q :=
    (mul_le_mul_of_nonneg_left hwlo hpow.le).trans hlinhi
  have hloglo := Real.log_le_log hq hlo
  have hloghi := Real.log_le_log (mul_pos hpow hu) hhi
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (mul_pos hpow hu).ne',
    Real.log_mul hpow.ne' hu.ne', Real.log_pow] at hloglo
  rw [Real.log_mul hpow.ne' hu.ne', Real.log_pow,
    Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hq.ne'] at hloghi
  change -Real.log 2 ≤ s.count * Real.log phi + Real.log (s.u : ℝ) - Real.log q ∧
    s.count * Real.log phi + Real.log (s.u : ℝ) - Real.log q ≤ Real.log 3
  constructor <;> linarith

private theorem bounded_div_tendsto {f : ℕ → ℝ} {lo hi : ℝ}
    (h : ∀ n ≥ 1, lo ≤ f n ∧ f n ≤ hi) :
    Tendsto (fun n : ℕ => f n / (n : ℝ)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_div_atTop_nhds_zero_nat lo)
    (tendsto_const_div_atTop_nhds_zero_nat hi)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_le_div_of_nonneg_right (h n hn).1 (Nat.cast_nonneg n)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_le_div_of_nonneg_right (h n hn).2 (Nat.cast_nonneg n)

private theorem unreduced_height_scale
    (hdelta : Tendsto (fun n : ℕ => -Real.log (delta n) / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Real.log ((decimalSplit n).u : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log 10 / 2)) := by
  have herr := bounded_div_tendsto (fun _ hn => split_height_log_bounds hn)
  have hcombined := ((herr.sub hdelta).const_add (Real.log 10)).div_const 2
  rw [sub_zero, add_zero] at hcombined
  refine hcombined.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [log_decimalDenominator]
  field_simp
  ring

theorem residual_height_scale
    (hdelta : Tendsto (fun n : ℕ => -Real.log (delta n) / (n : ℝ)) atTop (𝓝 0))
    (hgcd : Tendsto (fun n : ℕ => Real.log (commonFactor n : ℝ) / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Real.log (residualU n : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log 10 / 2)) := by
  have h := (unreduced_height_scale hdelta).sub hgcd
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hu : 0 < residualU n := by
    have := residual_twice_le hn
    have := residualV_pos hn
    omega
  have hu0 : (residualU n : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  have hd0 : (commonFactor n : ℝ) ≠ 0 := by exact_mod_cast (commonFactor_pos n).ne'
  have hcast : (residualU n : ℝ) * (commonFactor n : ℝ) = ((decimalSplit n).u : ℝ) := by
    exact_mod_cast (residual_exact hn).1
  rw [← hcast, Real.log_mul hu0 hd0]
  ring

theorem prefix_scale
    (hdelta : Tendsto (fun n : ℕ => -Real.log (delta n) / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ((decimalSplit n).count : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log 10 / (2 * Real.log phi))) := by
  have herr := bounded_div_tendsto (fun _ hn => split_prefix_log_bounds hn)
  have hcombined := ((herr.sub (unreduced_height_scale hdelta)).const_add
    (Real.log 10)).div_const (Real.log phi)
  have hlim : (Real.log 10 + (0 - Real.log 10 / 2)) / Real.log phi =
      Real.log 10 / (2 * Real.log phi) := by ring
  rw [hlim] at hcombined
  refine hcombined.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hphi0 : Real.log phi ≠ 0 := (Real.log_pos (by linarith [phi_gt_three_halves])).ne'
  rw [log_decimalDenominator]
  field_simp
  ring

end GoldiLochs
