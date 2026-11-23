module

public import GoldiLochs.Split
import Mathlib.Tactic

/-! # Exact phase of the first quotient beyond the all-ones prefix -/

@[expose] public section

namespace GoldiLochs

theorem decimalSplit_phase {n : ℕ} (hn : 1 ≤ n) :
    let s := decimalSplit n
    delta n * phi ^ (2 * s.count) * ((s.u : ℝ) + (phi - 1) * (s.v : ℝ)) =
      ((s.u : ℝ) - phi * (s.v : ℝ)) *
        (Real.sqrt 5 * (decimalDenominator n : ℝ) - delta n) := by
  let s := decimalSplit n
  let q : ℝ := decimalDenominator n
  have hsqrt : 2 * phi - 1 = Real.sqrt 5 := by unfold phi; ring
  obtain ⟨hplus, hminus⟩ :=
    stripOnes_linear (truncationNumeratorExact n) (decimalDenominator n)
  change phi ^ s.count * ((s.u : ℝ) + (phi - 1) * (s.v : ℝ)) =
    (truncationNumeratorExact n : ℝ) + (phi - 1) * q at hplus
  change (s.u : ℝ) - phi * (s.v : ℝ) =
    (-phi) ^ s.count * ((truncationNumeratorExact n : ℝ) - phi * q) at hminus
  rw [← truncationNumerator_eq_exact] at hplus hminus
  have hplus' : phi ^ s.count * ((s.u : ℝ) + (phi - 1) * (s.v : ℝ)) =
      Real.sqrt 5 * q - delta n := by
    rw [hplus, ← hsqrt]
    change (truncationNumerator n : ℝ) + (phi - 1) * q =
      (2 * phi - 1) * q - (phi * q - (truncationNumerator n : ℝ))
    ring
  have hminus' : (s.u : ℝ) - phi * (s.v : ℝ) = phi ^ s.count * delta n := by
    have heq : (truncationNumerator n : ℝ) - phi * q = -delta n := by
      unfold delta q
      ring
    rw [hminus, heq, (decimalSplit_odd hn).neg_pow]
    ring
  change delta n * phi ^ (2 * s.count) * ((s.u : ℝ) + (phi - 1) * (s.v : ℝ)) =
    ((s.u : ℝ) - phi * (s.v : ℝ)) * (Real.sqrt 5 * q - delta n)
  rw [hminus', ← hplus', two_mul, pow_add]
  ring

/-- Ratio of the two linear forms at the end of the initial run of ones. -/
noncomputable def residualPhase (n : ℕ) : ℝ :=
  let s := decimalSplit n
  ((s.u : ℝ) - phi * (s.v : ℝ)) / ((s.u : ℝ) + (phi - 1) * (s.v : ℝ))

private theorem phase_denom_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < ((decimalSplit n).u : ℝ) + (phi - 1) * ((decimalSplit n).v : ℝ) := by
  obtain ⟨hv, hu, _, _⟩ := decimalSplit_spec hn
  have hu0 : 0 < ((decimalSplit n).u : ℝ) := by
    exact_mod_cast (show 0 < (decimalSplit n).u by omega)
  have hphi : 0 ≤ phi - 1 := by linarith [phi_gt_three_halves]
  exact lt_of_lt_of_le hu0 (le_add_of_nonneg_right (mul_nonneg hphi (Nat.cast_nonneg _)))

theorem residualPhase_eq {n : ℕ} (hn : 1 ≤ n) :
    residualPhase n = phi ^ (2 * (decimalSplit n).count) * delta n /
      (Real.sqrt 5 * (decimalDenominator n : ℝ) - delta n) := by
  have hq : 0 < (decimalDenominator n : ℝ) := by exact_mod_cast decimalDenominator_pos n
  unfold residualPhase
  apply (div_eq_div_iff (phase_denom_pos hn).ne' (hq.trans (delta_factor_bounds n).1).ne').2
  simpa only [mul_comm (delta n), eq_comm] using decimalSplit_phase hn

theorem residualPhase_bounds {n : ℕ} (hn : 1 ≤ n) :
    (phi ^ 4)⁻¹ ≤ residualPhase n ∧ residualPhase n < 1 := by
  let s := decimalSplit n
  have hv : 0 < (s.v : ℝ) := by exact_mod_cast (decimalSplit_spec hn).1
  have hu : 2 * (s.v : ℝ) ≤ (s.u : ℝ) := by exact_mod_cast (decimalSplit_spec hn).2.1
  have hphi : 0 < phi := by linarith [phi_gt_three_halves]
  have hphi4 : phi ^ 4 = 3 * phi + 2 := by
    calc
      phi ^ 4 = (phi ^ 2) ^ 2 := by ring
      _ = (phi + 1) ^ 2 := by rw [phi_sq]
      _ = 3 * phi + 2 := by nlinarith [phi_sq]
  have hcross : (s.u : ℝ) + (phi - 1) * (s.v : ℝ) ≤
      ((s.u : ℝ) - phi * (s.v : ℝ)) * phi ^ 4 := by
    rw [hphi4]
    have hr : ((s.u : ℝ) - phi * (s.v : ℝ)) * (3 * phi + 2) -
        ((s.u : ℝ) + (phi - 1) * (s.v : ℝ)) =
        (3 * phi + 1) * ((s.u : ℝ) - 2 * (s.v : ℝ)) := by
      linear_combination (-3 * (s.v : ℝ)) * phi_sq
    have hnonneg : 0 ≤ (3 * phi + 1) * ((s.u : ℝ) - 2 * (s.v : ℝ)) :=
      mul_nonneg (by linarith) (sub_nonneg.mpr hu)
    linarith
  constructor
  · unfold residualPhase
    rw [inv_eq_one_div]
    exact (div_le_div_iff₀ (pow_pos hphi _) (phase_denom_pos hn)).2 (by simpa using hcross)
  · unfold residualPhase
    apply (div_lt_one (phase_denom_pos hn)).2
    change (s.u : ℝ) - phi * (s.v : ℝ) < (s.u : ℝ) + (phi - 1) * (s.v : ℝ)
    nlinarith [mul_pos (show 0 < 2 * phi - 1 by linarith [phi_gt_three_halves]) hv]

end GoldiLochs
