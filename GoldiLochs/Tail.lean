module

public import GoldiLochs.Remainders
public import GoldiLochs.Split
import Mathlib.Tactic

/-! # The deterministic tail law and its relation to the target -/

@[expose] public section

open Filter
open scoped BigOperators

namespace GoldiLochs

/-- The conjectured number of tail divisions per unit of log height. -/
noncomputable def euclideanRate : ℝ := 12 * Real.log 2 / Real.pi ^ 2

/-- The candidate mean of the negative log of a remainder ratio. -/
noncomputable def gaussLogMean : ℝ := Real.pi ^ 2 / (12 * Real.log 2)

/-- The unproved rate law for the particular decimal-truncation tail. -/
def TailLaw : Prop :=
  Tendsto (fun n : ℕ => (tailDepth n : ℝ) / Real.log (residualU n : ℝ))
    atTop (nhds euclideanRate)

/-- The sum of the negative log of each consecutive ratio in the reduced decimal tail. -/
noncomputable def tailLogSum (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (tailDepth n),
    -Real.log ((euclidRemainder (residualU n) (residualV n) (j + 1) : ℝ) /
      euclidRemainder (residualU n) (residualV n) j)

/-- The equivalent unproved logarithmic mean law for the same finite orbits. -/
def TailMeanLaw : Prop :=
  Tendsto (fun n : ℕ => tailLogSum n / (tailDepth n : ℝ)) atTop (nhds gaussLogMean)

private theorem log_residualU_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < Real.log (residualU n : ℝ) := by
  apply Real.log_pos
  have := residualV_pos hn
  have := residual_twice_le hn
  exact_mod_cast (show 1 < residualU n by omega)

/-- The actual decimal tail telescopes to its log height. -/
theorem tailLogSum_eq_log_residualU {n : ℕ} (hn : 1 ≤ n) :
    tailLogSum n = Real.log (residualU n : ℝ) := by
  have hU := residual_twice_le hn
  have hV := residualV_pos hn
  exact sum_neg_log_remainder_ratios_of_coprime (show 0 < residualU n by omega)
    (residual_coprime hn)

theorem tailLaw_iff_tailMeanLaw : TailLaw ↔ TailMeanLaw := by
  have hRate : 0 < euclideanRate := by unfold euclideanRate; positivity
  have hMean : 0 < gaussLogMean := by unfold gaussLogMean; positivity
  have hRateInv : euclideanRate⁻¹ = gaussLogMean := by
    rw [euclideanRate, gaussLogMean, inv_div]
  have hMeanInv : gaussLogMean⁻¹ = euclideanRate := by
    rw [← hRateInv, inv_inv]
  unfold TailLaw TailMeanLaw
  constructor
  · intro h
    have hInv := h.inv₀ hRate.ne'
    rw [hRateInv] at hInv
    apply hInv.congr'
    refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    simp only [inv_div, tailLogSum_eq_log_residualU hn]
  · intro h
    have hInv := h.inv₀ hMean.ne'
    rw [hMeanInv] at hInv
    apply hInv.congr'
    refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    simp only [inv_div, tailLogSum_eq_log_residualU hn]

/-- Once the prefix and residual-height scales are established, the original pointwise
target is equivalent to the rate law for the selected reduced tails. -/
theorem target_iff_tailLaw_of_scales
    (prefixScale : Tendsto (fun n : ℕ => ((decimalSplit n).count : ℝ) / (n : ℝ))
      atTop (nhds (Real.log 10 / (2 * Real.log phi))))
    (heightScale : Tendsto (fun n : ℕ => Real.log (residualU n : ℝ) / (n : ℝ))
      atTop (nhds (Real.log 10 / 2))) :
    Target ↔ TailLaw := by
  let A := Real.log 10 / (2 * Real.log phi)
  let B := Real.log 10 / 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hConstant : proposedConstant = A + euclideanRate * B := by
    unfold A B proposedConstant euclideanRate
    ring
  unfold Target TailLaw
  constructor
  · intro h
    have hDiff := (h.sub prefixScale).div heightScale hB.ne'
    change Tendsto _ atTop (nhds ((proposedConstant - A) / B)) at hDiff
    have hLimit : (proposedConstant - A) / B = euclideanRate := by
      rw [hConstant, add_sub_cancel_left, mul_div_cancel_right₀ _ hB.ne']
    rw [hLimit] at hDiff
    apply hDiff.congr'
    refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    change ((depth n : ℝ) / n - ((decimalSplit n).count : ℝ) / n) /
      (Real.log (residualU n : ℝ) / n) =
      (tailDepth n : ℝ) / Real.log (residualU n : ℝ)
    rw [depth_eq_prefix_add_tail hn, Nat.cast_add, ← sub_div, add_sub_cancel_left,
      div_div_div_cancel_right₀ (show (n : ℝ) ≠ 0 by exact_mod_cast (show n ≠ 0 by omega))]
  · intro h
    have hSum := prefixScale.add (h.mul heightScale)
    change Tendsto _ atTop (nhds (A + euclideanRate * B)) at hSum
    rw [← hConstant] at hSum
    apply hSum.congr'
    refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    change ((decimalSplit n).count : ℝ) / n +
      ((tailDepth n : ℝ) / Real.log (residualU n : ℝ)) *
        (Real.log (residualU n : ℝ) / n) = (depth n : ℝ) / n
    rw [← mul_div_assoc, div_mul_cancel₀ _ (log_residualU_pos hn).ne', ← add_div,
      depth_eq_prefix_add_tail hn, Nat.cast_add]

end GoldiLochs
