module

public import GoldiLochs.Continuants
public import GoldiLochs.Scale
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Combining forward and reverse bounds on a tail quotient -/

public section

open Filter
open scoped Topology

namespace GoldiLochs

/-- A weighted lower bound on the error and a convergent upper bound constrain the
next digit in terms of the previous denominator. -/
theorem quotient_le_of_weighted_error {a q gain error : ℝ}
    (ha : 0 < a) (hq : 0 < q) (hg : 0 < gain) (m : ℕ)
    (hlower : gain⁻¹ ≤ q ^ (m + 2) * error)
    (hupper : error ≤ 1 / (a * q ^ 2)) :
    a ≤ gain * q ^ m := by
  have h := hlower.trans (mul_le_mul_of_nonneg_left hupper (pow_nonneg hq.le _))
  have heq : q ^ (m + 2) * (1 / (a * q ^ 2)) = q ^ m / a := by
    rw [pow_add]
    field_simp
  rw [heq, inv_eq_one_div] at h
  simpa [one_mul, mul_comm] using (div_le_div_iff₀ hg ha).mp h

/-- The left-hand estimate suffices when the right continuant is large. For a
smaller right continuant only the localized reverse estimate is needed. -/
theorem log_quotient_bound_of_two_ends {a left right u q ε : ℝ}
    (ha : 0 < a) (hl : 0 < left) (hr : 0 < right) (hq : 1 < q)
    (hsize : Real.log u / Real.log q ≤ 1 / 2 + ε)
    (hprod : a * left * right ≤ u)
    (hleft : a ≤ q ^ ε * left ^ 2)
    (hright : right ≤ q ^ (1 / 8 : ℝ) → a ≤ q ^ ε * right ^ 2) :
    Real.log a / Real.log q ≤ 1 / 4 + ε := by
  have hq' := zero_lt_one.trans hq
  have hlog := Real.log_pos hq
  have hsize' := (div_le_iff₀ hlog).mp hsize
  have hgain := Real.rpow_pos_of_pos hq' ε
  have hp := Real.log_le_log (mul_pos (mul_pos ha hl) hr) hprod
  rw [Real.log_mul (mul_pos ha hl).ne' hr.ne', Real.log_mul ha.ne' hl.ne'] at hp
  have hf := Real.log_le_log ha hleft
  rw [Real.log_mul hgain.ne' (pow_ne_zero _ hl.ne'), Real.log_rpow hq', Real.log_pow] at hf
  push_cast at hf
  apply (div_le_iff₀ hlog).mpr
  by_cases hs : right ≤ q ^ (1 / 8 : ℝ)
  · have hb := Real.log_le_log ha (hright hs)
    rw [Real.log_mul hgain.ne' (pow_ne_zero _ hr.ne'), Real.log_rpow hq', Real.log_pow] at hb
    push_cast at hb
    linarith
  · have hb := Real.log_le_log (Real.rpow_pos_of_pos hq' (1 / 8 : ℝ)) (le_of_not_ge hs)
    rw [Real.log_rpow hq'] at hb
    linarith

theorem residual_height_scale_log_denominator
    (hheight : Tendsto (fun n : ℕ => Real.log (residualU n : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log 10 / 2))) :
    Tendsto (fun n : ℕ => Real.log (residualU n : ℝ) / Real.log (decimalDenominator n : ℝ))
      atTop (𝓝 (1 / 2)) := by
  have hlog : Real.log 10 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hlim : Real.log 10 / 2 / Real.log 10 = 1 / 2 := by field_simp
  have h := hheight.div_const (Real.log 10)
  rw [hlim] at h
  apply h.congr'
  exact Eventually.of_forall (fun n => by
    dsimp
    rw [log_decimalDenominator, div_div])

/-- The fourth-power-weighted error condition for a reduced rational center distinct
from the given ratio. -/
def FourthPowerSeparation (x lower : ℝ) (p q : ℕ) : Prop :=
  0 < q → p ≤ q → p.Coprime q → 0 < |x - (p : ℝ) / q| →
    lower ≤ (q : ℝ) ^ 4 * |x - (p : ℝ) / q|

/-- A global forward separation and a local reverse separation bound the logarithm
of every quotient in the actual residual word. The Diophantine hypotheses are explicit. -/
theorem eventually_log_tail_quotient_le_quarter
    (hheight : Tendsto (fun n : ℕ => Real.log (residualU n : ℝ) / (n : ℝ))
      atTop (𝓝 (Real.log 10 / 2)))
    (hforward : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ p q : ℕ,
      FourthPowerSeparation ((residualV n : ℝ) / residualU n)
        (((decimalDenominator n : ℝ) ^ ε)⁻¹) p q)
    (hreverse : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ p q : ℕ,
      (q : ℝ) ≤ (decimalDenominator n : ℝ) ^ (1 / 8 : ℝ) →
      FourthPowerSeparation
        (((penultimatePair (residualU n) (residualV n)).2 : ℝ) / residualU n)
        (((decimalDenominator n : ℝ) ^ ε)⁻¹) p q) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ a ∈ euclidDigits (residualU n) (residualV n),
      Real.log (a : ℝ) / Real.log (decimalDenominator n : ℝ) ≤ 1 / 4 + ε := by
  intro ε hε
  have hscale := residual_height_scale_log_denominator hheight
  have hsize := (tendsto_order.mp hscale).2 (1 / 2 + ε) (by linarith)
  filter_upwards [hforward ε hε, hreverse ε hε, hsize, eventually_ge_atTop 1]
    with n hfw hrw hsz hn a ha
  obtain ⟨pre, post, hword⟩ := List.append_of_mem ha
  have hapos : 0 < (a : ℝ) := by exact_mod_cast residualDigits_pos hn a ha
  have hq : 1 < (decimalDenominator n : ℝ) := by
    have h10 : 10 ≤ decimalDenominator n := by
      simpa [decimalDenominator] using Nat.pow_le_pow_right (by decide : 0 < 10) hn
    exact_mod_cast (show 1 < decimalDenominator n by omega)
  have hgain := Real.rpow_pos_of_pos (zero_lt_one.trans hq) ε
  obtain ⟨hl, hlr, hlc, hln, hlu⟩ := residual_digit_approximation_left hn pre post hword
  obtain ⟨hr, hrr, hrc, hrn, hru⟩ := residual_digit_approximation_right hn pre post hword
  have hlpos : 0 < (continuant pre : ℝ) := by exact_mod_cast hl
  have hrpos : 0 < (continuant post : ℝ) := by exact_mod_cast hr
  have hprod : (a : ℝ) * (continuant pre : ℝ) * (continuant post : ℝ) ≤ (residualU n : ℝ) :=
    by exact_mod_cast tail_digit_continuant_bound hn pre post hword
  apply log_quotient_bound_of_two_ends hapos hlpos hrpos hq hsz.le hprod
  · exact quotient_le_of_weighted_error hapos hlpos hgain 2
      (hfw _ _ hl hlr hlc hln) hlu
  · intro hs
    exact quotient_le_of_weighted_error hapos hrpos hgain 2
      (hrw _ _ hs hr hrr hrc hrn) hru

end GoldiLochs
