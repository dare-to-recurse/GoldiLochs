module

public import GoldiLochs.Definitions
public import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-! # Exact integer arithmetic for the decimal truncations -/

@[expose] public section

namespace GoldiLochs

theorem phi_gt_three_halves : (3 : ℝ) / 2 < phi := by
  have h : (2 : ℝ) < Real.sqrt 5 := Real.lt_sqrt_of_sq_lt (by norm_num)
  unfold phi
  linarith

theorem phi_sq : phi ^ 2 = phi + 1 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  unfold phi
  nlinarith

theorem phi_irrational : Irrational phi := by
  have h : Irrational (Real.sqrt 5) :=
    (show Nat.Prime 5 by decide).irrational_sqrt
  simpa [phi] using (h.natCast_add 1).div_natCast (m := 2) (by decide)

theorem decimalDenominator_pos (n : ℕ) : 0 < decimalDenominator n :=
  pow_pos (by decide) _

/-- The fractional part discarded by decimal truncation. -/
noncomputable def delta (n : ℕ) : ℝ :=
  phi * (decimalDenominator n : ℝ) - (truncationNumerator n : ℝ)

theorem delta_pos (n : ℕ) : 0 < delta n := by
  have hq : 0 < (decimalDenominator n : ℝ) := by exact_mod_cast decimalDenominator_pos n
  have hp : 0 < phi := by linarith [phi_gt_three_halves]
  have hle := Nat.floor_le (mul_nonneg hp.le hq.le)
  have hne := (phi_irrational.mul_natCast (Nat.ne_of_gt (decimalDenominator_pos n))).ne_nat
    (truncationNumerator n)
  exact sub_pos.mpr (lt_of_le_of_ne hle (Ne.symm hne))

theorem delta_lt_one (n : ℕ) : delta n < 1 :=
  sub_lt_iff_lt_add'.mpr (Nat.lt_floor_add_one _)

theorem denominator_lt_numerator {n : ℕ} (hn : 1 ≤ n) :
    decimalDenominator n < truncationNumerator n := by
  have hq : 10 ≤ decimalDenominator n := by
    simpa [decimalDenominator] using (Nat.pow_le_pow_right (by decide : 0 < 10) hn)
  have hqR : (10 : ℝ) ≤ (decimalDenominator n : ℝ) := by exact_mod_cast hq
  have hstep := mul_lt_mul_of_pos_right phi_gt_three_halves (by positivity :
    0 < (decimalDenominator n : ℝ))
  have hdelta := delta_lt_one n
  unfold delta at hdelta
  exact_mod_cast (show (decimalDenominator n : ℝ) < (truncationNumerator n : ℝ) by
    linarith)

/-- The same numerator using only natural-number arithmetic. -/
def truncationNumeratorExact (n : ℕ) : ℕ :=
  (decimalDenominator n + Nat.sqrt (5 * decimalDenominator n ^ 2)) / 2

theorem truncationNumerator_eq_exact (n : ℕ) :
    truncationNumerator n = truncationNumeratorExact n := by
  let q := decimalDenominator n
  let s := Nat.sqrt (5 * q ^ 2)
  let a := (q + s) / 2
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hsloNat : s ^ 2 ≤ 5 * q ^ 2 := Nat.sqrt_le' _
  have hshiNat : 5 * q ^ 2 < (s + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hslo : (s : ℝ) ^ 2 ≤ 5 * (q : ℝ) ^ 2 := by exact_mod_cast hsloNat
  have hshi : 5 * (q : ℝ) ^ 2 < ((s : ℝ) + 1) ^ 2 := by exact_mod_cast hshiNat
  have hsquare : (Real.sqrt 5 * (q : ℝ)) ^ 2 = 5 * (q : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  have hsqrt : 0 ≤ Real.sqrt 5 * (q : ℝ) := mul_nonneg (Real.sqrt_nonneg _) hq
  have hlo : (s : ℝ) ≤ Real.sqrt 5 * (q : ℝ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) s]
  have hhi : Real.sqrt 5 * (q : ℝ) < (s : ℝ) + 1 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) s]
  have halo : 2 * a ≤ q + s := by dsimp [a]; omega
  have hahi : q + s + 1 ≤ 2 * (a + 1) := by dsimp [a]; omega
  have haloR : 2 * (a : ℝ) ≤ (q : ℝ) + s := by exact_mod_cast halo
  have hahiR : (q : ℝ) + s + 1 ≤ 2 * ((a : ℝ) + 1) := by exact_mod_cast hahi
  change Nat.floor (phi * (q : ℝ)) = a
  apply (Nat.floor_eq_iff (by linarith [mul_nonneg (show 0 ≤ phi by
    linarith [phi_gt_three_halves]) hq])).2
  unfold phi
  constructor <;> nlinarith

end GoldiLochs
