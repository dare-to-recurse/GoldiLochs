module

public import GoldiLochs.Definitions
public import Mathlib.Algebra.ContinuedFractions.Computation.Approximations
public import Mathlib.Algebra.ContinuedFractions.Computation.CorrectnessTerminating
public import Mathlib.Data.Rat.Floor

/-! # Euclidean depth and canonical regular continued fractions -/

public section

namespace GoldiLochs

@[simp] theorem euclidDepth_zero (a : ℕ) : euclidDepth a 0 = 0 := by
  rw [euclidDepth]
  rfl

theorem euclidDepth_step (a : ℕ) {b : ℕ} (hb : 0 < b) :
    euclidDepth a b = 1 + euclidDepth b (a % b) := by
  rw [euclidDepth, dite_eq_right hb.ne']

/-- Multiplication by a common positive factor preserves the complete Euclidean depth. -/
theorem euclidDepth_mul (a b : ℕ) {d : ℕ} (hd : 0 < d) :
    euclidDepth (d * a) (d * b) = euclidDepth a b := by
  by_cases hb : b = 0
  · simp [hb]
  · have hb' := Nat.pos_of_ne_zero hb
    rw [euclidDepth_step _ (Nat.mul_pos hd hb'), euclidDepth_step a hb',
      Nat.mul_mod_mul_left, euclidDepth_mul b (a % b) hd]
termination_by b
decreasing_by exact Nat.mod_lt _ hb'

/-- Cancellation to lowest terms preserves the complete Euclidean depth. -/
theorem euclidDepth_div_gcd (a : ℕ) {b : ℕ} (hb : 0 < b) :
    euclidDepth (a / a.gcd b) (b / a.gcd b) = euclidDepth a b := by
  have hd := Nat.gcd_pos_of_pos_right a hb
  rw [← euclidDepth_mul (a / a.gcd b) (b / a.gcd b) hd,
    Nat.mul_div_cancel' (Nat.gcd_dvd_left a b), Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)]

/-- The Euclidean step preserves the greatest common divisor. -/
theorem gcd_mod_step (a b : ℕ) : b.gcd (a % b) = a.gcd b := by
  rw [Nat.gcd_comm b (a % b), ← Nat.gcd_rec, Nat.gcd_comm]

open GenContFract GenContFract.IntFractPair

/-- The integer/fractional-part stream underlying mathlib's regular continued fraction first
stops at the Euclidean depth, with its index zero representing the integer part. -/
theorem cf_stream_eq_none_iff (a : ℕ) {b : ℕ} (hb : 0 < b) (i : ℕ) :
    IntFractPair.stream ((a : ℚ) / b) i = none ↔ euclidDepth a b ≤ i := by
  induction i generalizing a b with
  | zero => simp [stream_zero, euclidDepth_step a hb]
  | succ i ih =>
    rw [euclidDepth_step a hb]
    have hf : Int.fract ((a : ℚ) / b) = ((a % b : ℕ) : ℚ) / b :=
      Int.fract_div_natCast_eq_div_natCast_mod
    by_cases hm : a % b = 0
    · have hzero : Int.fract ((a : ℚ) / b) = 0 := by simp [hf, hm]
      obtain ⟨z, hz⟩ := Int.fract_eq_zero_iff.mp hzero
      have hz' : (z : ℚ) = (a : ℚ) / b := hz
      rw [← hz', stream_succ_of_int]
      simp [hm]
    · have hfract : Int.fract ((a : ℚ) / b) ≠ 0 := by
        rw [hf]
        exact div_ne_zero (by exact_mod_cast hm) (by exact_mod_cast hb.ne')
      rw [stream_succ hfract, hf, inv_div, ih b (Nat.pos_of_ne_zero hm)]
      omega

/-- The first missing entry in the sequence after the integer part has index one smaller
than the complete Euclidean depth. -/
theorem cf_terminatedAt_iff (a : ℕ) {b : ℕ} (hb : 0 < b) (i : ℕ) :
    (GenContFract.of ((a : ℚ) / b)).TerminatedAt i ↔ euclidDepth a b ≤ i + 1 :=
  of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.trans
    (cf_stream_eq_none_iff a hb (i + 1))

/-- The last convergent at the Euclidean depth is the original rational number. -/
theorem cf_last_convergent (a : ℕ) {b : ℕ} (hb : 0 < b) :
    (GenContFract.of ((a : ℚ) / b)).convs (euclidDepth a b - 1) = (a : ℚ) / b :=
  (of_correctness_of_nth_stream_eq_none
    ((cf_stream_eq_none_iff a hb _).mpr le_rfl)).symm

/-- The final coefficient of a finite regular continued fraction is at least two whenever
it occurs after the integer part. -/
theorem cf_final_coefficient_ge_two {q : ℚ} {i : ℕ} {p : IntFractPair ℚ}
    (h : IntFractPair.stream q (i + 1) = some p)
    (hstop : IntFractPair.stream q (i + 1 + 1) = none) : 2 ≤ p.b := by
  have hp : p.fr = 0 := by
    rcases succ_nth_stream_eq_none_iff.mp hstop with hnone | ⟨p', h', hzero⟩
    · simp [h] at hnone
    · have heq : p = p' := Option.some.inj (h.symm.trans h')
      rwa [heq]
  obtain ⟨r, hr, hrne, rfl⟩ := succ_nth_stream_eq_some_iff.mp h
  have hrpos : 0 < r.fr := lt_of_le_of_ne (nth_stream_fr_nonneg hr) (Ne.symm hrne)
  have hinv : 1 < r.fr⁻¹ := (one_lt_inv₀ hrpos).mpr (nth_stream_fr_lt_one hr)
  change Int.fract (r.fr⁻¹) = 0 at hp
  have hval : r.fr⁻¹ = (⌊r.fr⁻¹⌋ : ℚ) := sub_eq_zero.mp hp
  rw [hval] at hinv
  change 2 ≤ ⌊r.fr⁻¹⌋
  have : (1 : ℤ) < ⌊r.fr⁻¹⌋ := by exact_mod_cast hinv
  omega

/-- For a noninteger nonnegative rational, the final coefficient at index
`euclidDepth a b - 1` satisfies the canonical lower bound. -/
theorem cf_last_coefficient_ge_two (a : ℕ) {b : ℕ} (hb : 0 < b) (hm : a % b ≠ 0) :
    ∃ p, IntFractPair.stream ((a : ℚ) / b) (euclidDepth a b - 1) = some p ∧
      2 ≤ p.b := by
  have hdepth : 1 < euclidDepth a b := by
    rw [euclidDepth_step a hb, euclidDepth_step b (Nat.pos_of_ne_zero hm)]
    omega
  have hlast : IntFractPair.stream ((a : ℚ) / b) (euclidDepth a b - 1) ≠ none := by
    intro hnone
    have := (cf_stream_eq_none_iff a hb _).mp hnone
    omega
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp hlast
  refine ⟨p, hp, cf_final_coefficient_ge_two (q := (a : ℚ) / b) (i := euclidDepth a b - 2) ?_ ?_⟩
  · rwa [show euclidDepth a b - 2 + 1 = euclidDepth a b - 1 by omega]
  · rw [show euclidDepth a b - 2 + 1 + 1 = euclidDepth a b by omega]
    exact (cf_stream_eq_none_iff a hb _).mpr le_rfl

end GoldiLochs
