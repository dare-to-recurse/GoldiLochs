module

public import GoldiLochs.Euclid
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Euclidean remainders and the logarithmic sum over a finite orbit -/

@[expose] public section

open scoped BigOperators

namespace GoldiLochs

/-- The Euclidean remainder with index zero equal to `a` and index one equal to `b`.
After the first zero remainder, the sequence stays zero. -/
def euclidRemainder (a b : ℕ) : ℕ → ℕ
  | 0 => a
  | i + 1 => if b = 0 then 0 else euclidRemainder b (a % b) i

@[simp] theorem euclidRemainder_zero (a b : ℕ) : euclidRemainder a b 0 = a := rfl

@[simp] theorem euclidRemainder_succ_of_zero (a i : ℕ) :
    euclidRemainder a 0 (i + 1) = 0 := rfl

theorem euclidRemainder_step (a : ℕ) {b : ℕ} (hb : 0 < b) (i : ℕ) :
    euclidRemainder a b (i + 1) = euclidRemainder b (a % b) i := by
  rw [euclidRemainder, ite_eq_right hb.ne']

@[simp] theorem euclidRemainder_one (a b : ℕ) : euclidRemainder a b 1 = b := by
  by_cases hb : b = 0
  · simp [hb]
  · simp [euclidRemainder_step a (Nat.pos_of_ne_zero hb) 0]

/-- For a positive initial numerator, the remainders are positive through the last division
and zero thereafter. -/
theorem euclidRemainder_pos_iff {a : ℕ} (ha : 0 < a) (b i : ℕ) :
    0 < euclidRemainder a b i ↔ i ≤ euclidDepth a b := by
  induction i generalizing a b with
  | zero => simp [ha]
  | succ i ih =>
    by_cases hb : b = 0
    · simp [hb]
    · have hb' := Nat.pos_of_ne_zero hb
      rw [euclidRemainder_step a hb', euclidDepth_step a hb', ih hb' (a % b)]
      omega

/-- The last nonzero remainder for positive input is the greatest common divisor. -/
theorem euclidRemainder_at_depth (a b : ℕ) :
    euclidRemainder a b (euclidDepth a b) = a.gcd b := by
  by_cases hb : b = 0
  · simp [hb]
  · have hb' := Nat.pos_of_ne_zero hb
    rw [euclidDepth_step a hb', Nat.add_comm 1, euclidRemainder_step a hb',
      euclidRemainder_at_depth b (a % b), gcd_mod_step]
termination_by b
decreasing_by exact Nat.mod_lt _ hb'

@[simp] theorem euclidRemainder_past_depth {a : ℕ} (ha : 0 < a) (b : ℕ) :
    euclidRemainder a b (euclidDepth a b + 1) = 0 := by
  apply Nat.eq_zero_of_not_pos
  rw [euclidRemainder_pos_iff ha]
  exact Nat.not_succ_le_self _

/-- The sum of negative logarithms of consecutive ratios telescopes up to any
index at most the Euclidean depth. -/
theorem sum_neg_log_remainder_ratios {a : ℕ} (ha : 0 < a) (b : ℕ) {i : ℕ}
    (hi : i ≤ euclidDepth a b) :
    (∑ j ∈ Finset.range i,
      -Real.log ((euclidRemainder a b (j + 1) : ℝ) / euclidRemainder a b j)) =
      Real.log (a : ℝ) - Real.log (euclidRemainder a b i : ℝ) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hil := Nat.le_of_succ_le hi
    have hj := (euclidRemainder_pos_iff ha b i).mpr hil
    have hj' := (euclidRemainder_pos_iff ha b (i + 1)).mpr hi
    rw [Finset.sum_range_succ, ih hil, Real.log_div (by positivity) (by positivity)]
    ring

/-- On reduced positive input, the sum over the complete Euclidean orbit equals
the logarithm of the initial numerator. -/
theorem sum_neg_log_remainder_ratios_of_coprime {a : ℕ} (ha : 0 < a) {b : ℕ}
    (hc : a.Coprime b) :
    (∑ j ∈ Finset.range (euclidDepth a b),
      -Real.log ((euclidRemainder a b (j + 1) : ℝ) / euclidRemainder a b j)) =
      Real.log (a : ℝ) := by
  rw [sum_neg_log_remainder_ratios ha b le_rfl, euclidRemainder_at_depth,
    Nat.coprime_iff_gcd_eq_one.mp hc]
  simp

end GoldiLochs
