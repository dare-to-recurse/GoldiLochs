module

public import GoldiLochs.Tail
public import Mathlib.Logic.Function.Iterate

/-! # Gauss map iterates along the reduced rational tails -/

@[expose] public section

open scoped BigOperators
open Function

namespace GoldiLochs

/-- The Gauss map, extended by zero at zero. -/
noncomputable def gaussMap (x : ℝ) : ℝ := Int.fract x⁻¹

/-- A positive divisor in the remainder sequence gives the next remainder by reduction
modulo that divisor. -/
theorem euclidRemainder_mod (a b i : ℕ) (h : 0 < euclidRemainder a b (i + 1)) :
    euclidRemainder a b (i + 2) = euclidRemainder a b i % euclidRemainder a b (i + 1) := by
  induction i generalizing a b with
  | zero =>
    have hb : 0 < b := by simpa using h
    rw [show 0 + 2 = 1 + 1 by rfl, euclidRemainder_step a hb, euclidRemainder_one,
      euclidRemainder_zero, euclidRemainder_one]
  | succ i ih =>
    have hb : 0 < b := by
      by_contra! h'
      have : b = 0 := Nat.eq_zero_of_le_zero h'
      simp [this] at h
    rw [euclidRemainder_step a hb] at h
    rw [euclidRemainder_step a hb, euclidRemainder_step a hb, euclidRemainder_step a hb]
    exact ih b (a % b) h

/-- Applying the Gauss map to a ratio of consecutive remainders gives the next ratio.
After the Euclidean algorithm stops, both sides are zero. -/
theorem gaussMap_remainder_ratio (a b i : ℕ) :
    gaussMap ((euclidRemainder a b (i + 1) : ℝ) / euclidRemainder a b i) =
      (euclidRemainder a b (i + 2) : ℝ) / euclidRemainder a b (i + 1) := by
  by_cases h : 0 < euclidRemainder a b (i + 1)
  · rw [gaussMap, inv_div, Int.fract_div_natCast_eq_div_natCast_mod, euclidRemainder_mod a b i h]
  · have hz := Nat.eq_zero_of_not_pos h
    simp [gaussMap, hz]

/-- Iterating the Gauss map from the ratio `b/a` gives exactly the Euclidean remainder ratios,
starting with the first ratio at iteration zero. -/
theorem gaussMap_iterate_eq_remainder_ratio (a b i : ℕ) :
    gaussMap^[i] ((b : ℝ) / a) =
      (euclidRemainder a b (i + 1) : ℝ) / euclidRemainder a b i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, gaussMap_remainder_ratio]

/-- The Gauss orbit stays positive for exactly the Euclidean depth. -/
theorem gaussMap_iterate_pos_iff {a : ℕ} (ha : 0 < a) (b i : ℕ) :
    0 < gaussMap^[i] ((b : ℝ) / a) ↔ i < euclidDepth a b := by
  rw [gaussMap_iterate_eq_remainder_ratio]
  by_cases h : i < euclidDepth a b
  · have hnum := (euclidRemainder_pos_iff ha b (i + 1)).mpr h
    have hden := (euclidRemainder_pos_iff ha b i).mpr h.le
    simp [h, div_pos (show 0 < (euclidRemainder a b (i + 1) : ℝ) by exact_mod_cast hnum)
      (show 0 < (euclidRemainder a b i : ℝ) by exact_mod_cast hden)]
  · have hnum : euclidRemainder a b (i + 1) = 0 := by
      apply Nat.eq_zero_of_not_pos
      exact fun hp => h ((euclidRemainder_pos_iff ha b (i + 1)).mp hp)
    simp [h, hnum]

/-- The deterministic tail sum samples the first `tailDepth n` iterates of the Gauss map
from `residualV n / residualU n`. -/
theorem tailLogSum_eq_gaussIterates (n : ℕ) :
    tailLogSum n =
      ∑ j ∈ Finset.range (tailDepth n),
        -Real.log (gaussMap^[j] ((residualV n : ℝ) / residualU n)) := by
  unfold tailLogSum
  apply Finset.sum_congr rfl
  intro j _
  rw [gaussMap_iterate_eq_remainder_ratio]

end GoldiLochs
