module

public import GoldiLochs.Euclid
public import GoldiLochs.Truncation
public import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-! # Euclidean decomposition after the maximal initial run of ones -/

@[expose] public section

namespace GoldiLochs

structure PrefixSplit where
  count : ℕ
  u : ℕ
  v : ℕ

/-- Each recursive call removes one leading quotient equal to one.
For inputs with `b < a`, the condition is equivalent to `a / b = 1`. -/
def stripOnes (a b : ℕ) : PrefixSplit :=
  if _h : b < a ∧ a < 2 * b then
    let rest := stripOnes b (a - b)
    { rest with count := rest.count + 1 }
  else ⟨0, a, b⟩
termination_by b
decreasing_by omega

private theorem mod_eq_sub_of_lt_twice {a b : ℕ} (hba : b ≤ a) (hab : a < 2 * b) :
    a % b = a - b := by
  rw [Nat.mod_eq_sub_mod hba, Nat.mod_eq_of_lt (by omega)]

theorem stripOnes_spec (a b : ℕ) (hba : b < a) (hb : 0 < b) :
    let s := stripOnes a b
    0 < s.v ∧ 2 * s.v ≤ s.u ∧
      euclidDepth a b = s.count + euclidDepth s.u s.v ∧
      Nat.gcd a b = Nat.gcd s.u s.v := by
  by_cases h : a < 2 * b
  · have hmod := mod_eq_sub_of_lt_twice hba.le h
    have ih := stripOnes_spec b (a - b) (by omega) (by omega)
    rw [stripOnes, dite_eq_left ⟨hba, h⟩, euclidDepth_step a hb, hmod]
    rcases ih with ⟨hv, hu, hdepth, hgcd⟩
    refine ⟨hv, hu, by dsimp; omega, ?_⟩
    calc
      Nat.gcd a b = Nat.gcd b (a % b) := (gcd_mod_step a b).symm
      _ = Nat.gcd b (a - b) := by rw [hmod]
      _ = _ := hgcd
  · rw [stripOnes, dite_eq_right (fun hh => h hh.2)]
    exact ⟨hb, Nat.le_of_not_gt h, by simp, rfl⟩
termination_by b
decreasing_by omega

/-- Twice-shifted reconstruction avoids a negative Fibonacci index at count zero. -/
theorem stripOnes_fib (a b : ℕ) :
    let s := stripOnes a b
    a = Nat.fib (s.count + 1) * s.u + Nat.fib s.count * s.v ∧
      a + b = Nat.fib (s.count + 2) * s.u + Nat.fib (s.count + 1) * s.v := by
  by_cases h : b < a ∧ a < 2 * b
  · have ih := stripOnes_fib b (a - b)
    rw [stripOnes, dite_eq_left h]
    rcases ih with ⟨ha, hab⟩
    have hsum : b + (a - b) = a := by omega
    dsimp at ha hab ⊢
    rw [hsum] at hab
    refine ⟨hab, ?_⟩
    rw [Nat.fib_add_two (n := (stripOnes b (a - b)).count + 1)]
    have hrec : Nat.fib ((stripOnes b (a - b)).count + 1 + 1) =
        Nat.fib (stripOnes b (a - b)).count + Nat.fib ((stripOnes b (a - b)).count + 1) :=
      Nat.fib_add_two
    simp only [← Nat.add_assoc, hrec, add_mul] at hab ⊢
    omega
  · rw [stripOnes, dite_eq_right h]
    simp
termination_by b
decreasing_by omega

/-- The form associated to the two roots of `X² - X - 1`. -/
def quadraticForm (u v : ℝ) : ℝ := u ^ 2 - u * v - v ^ 2

theorem quadraticForm_step (u v : ℝ) :
    quadraticForm v (u - v) = -quadraticForm u v := by
  unfold quadraticForm
  ring

theorem stripOnes_form (a b : ℕ) :
    let s := stripOnes a b
    quadraticForm (s.u : ℝ) (s.v : ℝ) =
      (-1 : ℝ) ^ s.count * quadraticForm (a : ℝ) (b : ℝ) := by
  by_cases h : b < a ∧ a < 2 * b
  · have ih := stripOnes_form b (a - b)
    rw [stripOnes, dite_eq_left h]
    dsimp at ih ⊢
    rw [ih, Nat.cast_sub h.1.le, quadraticForm_step, pow_succ]
    ring
  · rw [stripOnes, dite_eq_right h]
    simp
termination_by b
decreasing_by omega

/-- The two real linear forms that diagonalize the quotient-one step. -/
theorem stripOnes_linear (a b : ℕ) :
    let s := stripOnes a b
    phi ^ s.count * ((s.u : ℝ) + (phi - 1) * (s.v : ℝ)) =
      (a : ℝ) + (phi - 1) * (b : ℝ) ∧
    (s.u : ℝ) - phi * (s.v : ℝ) =
      (-phi) ^ s.count * ((a : ℝ) - phi * (b : ℝ)) := by
  by_cases h : b < a ∧ a < 2 * b
  · have ih := stripOnes_linear b (a - b)
    rw [stripOnes, dite_eq_left h]
    dsimp at ih ⊢
    rcases ih with ⟨hplus, hminus⟩
    rw [Nat.cast_sub h.1.le] at hplus hminus
    have hp : phi * (phi - 1) = 1 := by nlinarith [phi_sq]
    constructor
    · rw [pow_succ, mul_right_comm, hplus]
      calc
        _ = (phi * (phi - 1)) * (a : ℝ) + (phi - phi * (phi - 1)) * (b : ℝ) := by ring
        _ = _ := by rw [hp, one_mul]
    · rw [hminus, pow_succ, mul_assoc]
      congr 1
      calc
        _ = (1 + phi) * (b : ℝ) - phi * (a : ℝ) := by ring
        _ = (phi ^ 2) * (b : ℝ) - phi * (a : ℝ) := by rw [phi_sq, add_comm 1 phi]
        _ = _ := by ring
  · rw [stripOnes, dite_eq_right h]
    simp
termination_by b
decreasing_by omega

theorem quadraticForm_bounds {u v : ℝ} (hv : 0 < v) (hu : 2 * v ≤ u) :
    u ^ 2 / 4 ≤ quadraticForm u v ∧ quadraticForm u v < u ^ 2 := by
  have hu0 : 0 < u := by linarith
  unfold quadraticForm
  constructor
  · nlinarith [mul_nonneg (show 0 ≤ u - 2 * v by linarith)
      (show 0 ≤ 3 * u + 2 * v by linarith)]
  · nlinarith [mul_pos hu0 hv, sq_nonneg v]

theorem truncation_form (n : ℕ) :
    quadraticForm (truncationNumerator n : ℝ) (decimalDenominator n : ℝ) =
      -delta n * (Real.sqrt 5 * (decimalDenominator n : ℝ) - delta n) := by
  have hs : 2 * phi - 1 = Real.sqrt 5 := by unfold phi; ring
  have hq : phi ^ 2 - phi - 1 = 0 := by linarith [phi_sq]
  let q : ℝ := decimalDenominator n
  let e := delta n
  have ha : (truncationNumerator n : ℝ) = phi * q - e := by
    unfold e q delta
    ring
  rw [ha]
  change quadraticForm (phi * q - e) q = -e * (Real.sqrt 5 * q - e)
  rw [← hs]
  calc
    _ = (phi ^ 2 - phi - 1) * q ^ 2 - e * ((2 * phi - 1) * q - e) := by
      unfold quadraticForm
      ring
    _ = _ := by rw [hq, zero_mul, zero_sub, neg_mul]

/-- The surviving pair before cancellation. -/
def decimalSplit (n : ℕ) : PrefixSplit :=
  stripOnes (truncationNumeratorExact n) (decimalDenominator n)

/-- The common factor of the original truncation numerator and denominator. -/
def commonFactor (n : ℕ) : ℕ := (truncationNumeratorExact n).gcd (decimalDenominator n)

/-- The larger, reduced residual integer. -/
def residualU (n : ℕ) : ℕ := (decimalSplit n).u / commonFactor n

/-- The smaller, reduced residual integer. -/
def residualV (n : ℕ) : ℕ := (decimalSplit n).v / commonFactor n

/-- Euclidean depth after dropping the initial quotient run. -/
def tailDepth (n : ℕ) : ℕ := euclidDepth (residualU n) (residualV n)

theorem decimalSplit_spec {n : ℕ} (hn : 1 ≤ n) :
    0 < (decimalSplit n).v ∧ 2 * (decimalSplit n).v ≤ (decimalSplit n).u ∧
      depth n = (decimalSplit n).count + euclidDepth (decimalSplit n).u (decimalSplit n).v ∧
      commonFactor n = Nat.gcd (decimalSplit n).u (decimalSplit n).v := by
  unfold depth decimalSplit commonFactor
  rw [← truncationNumerator_eq_exact]
  exact stripOnes_spec _ _ (denominator_lt_numerator hn) (decimalDenominator_pos n)

theorem depth_eq_prefix_add_tail {n : ℕ} (hn : 1 ≤ n) :
    depth n = (decimalSplit n).count + tailDepth n := by
  rcases decimalSplit_spec hn with ⟨hv, _, hdepth, hgcd⟩
  rw [hdepth, tailDepth, residualU, residualV, hgcd, ← euclidDepth_div_gcd _ hv]

theorem commonFactor_pos (n : ℕ) : 0 < commonFactor n :=
  Nat.gcd_pos_of_pos_right _ (decimalDenominator_pos n)

theorem residual_exact {n : ℕ} (hn : 1 ≤ n) :
    residualU n * commonFactor n = (decimalSplit n).u ∧
      residualV n * commonFactor n = (decimalSplit n).v := by
  have h := (decimalSplit_spec hn).2.2.2
  exact ⟨Nat.div_mul_cancel (h ▸ Nat.gcd_dvd_left _ _),
    Nat.div_mul_cancel (h ▸ Nat.gcd_dvd_right _ _)⟩

theorem residual_coprime {n : ℕ} (hn : 1 ≤ n) :
    Nat.Coprime (residualU n) (residualV n) := by
  obtain ⟨hv, _, _, hgcd⟩ := decimalSplit_spec hn
  rw [residualU, residualV, hgcd]
  exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ hv)

theorem residualV_pos {n : ℕ} (hn : 1 ≤ n) : 0 < residualV n := by
  obtain ⟨hv, _, _, hgcd⟩ := decimalSplit_spec hn
  rw [residualV, hgcd]
  exact Nat.div_gcd_pos_of_pos_right _ hv

theorem residual_twice_le {n : ℕ} (hn : 1 ≤ n) : 2 * residualV n ≤ residualU n := by
  apply Nat.le_of_mul_le_mul_right _ (commonFactor_pos n)
  rw [Nat.mul_assoc, (residual_exact hn).1, (residual_exact hn).2]
  exact (decimalSplit_spec hn).2.1

theorem delta_factor_bounds (n : ℕ) :
    (decimalDenominator n : ℝ) < Real.sqrt 5 * (decimalDenominator n : ℝ) - delta n ∧
      Real.sqrt 5 * (decimalDenominator n : ℝ) - delta n < 3 * (decimalDenominator n : ℝ) := by
  have hq : (1 : ℝ) ≤ (decimalDenominator n : ℝ) := by
    exact_mod_cast decimalDenominator_pos n
  have hslo : (2 : ℝ) < Real.sqrt 5 := Real.lt_sqrt_of_sq_lt (by norm_num)
  have hshi : Real.sqrt 5 < (3 : ℝ) := (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  have hq0 : 0 < (decimalDenominator n : ℝ) := by linarith
  constructor
  · linarith [mul_lt_mul_of_pos_right hslo hq0, delta_lt_one n]
  · linarith [mul_lt_mul_of_pos_right hshi hq0, delta_pos n]

theorem decimalSplit_odd {n : ℕ} (hn : 1 ≤ n) : Odd (decimalSplit n).count := by
  obtain ⟨hv, hu, _, _⟩ := decimalSplit_spec hn
  have hb := quadraticForm_bounds (u := ((decimalSplit n).u : ℝ))
    (v := ((decimalSplit n).v : ℝ)) (by exact_mod_cast hv) (by exact_mod_cast hu)
  have hform := stripOnes_form (truncationNumerator n) (decimalDenominator n)
  have heq : stripOnes (truncationNumerator n) (decimalDenominator n) = decimalSplit n := by
    rw [decimalSplit, truncationNumerator_eq_exact]
  dsimp at hform
  rw [heq, truncation_form] at hform
  rcases Nat.even_or_odd (decimalSplit n).count with heven | hodd
  · rw [heven.neg_one_pow, one_mul] at hform
    have hfac : 0 < Real.sqrt 5 * (decimalDenominator n : ℝ) - delta n :=
      lt_trans (by exact_mod_cast decimalDenominator_pos n) (delta_factor_bounds n).1
    linarith [mul_neg_of_neg_of_pos (neg_lt_zero.mpr (delta_pos n)) hfac,
      sq_nonneg ((decimalSplit n).u : ℝ)]
  · exact hodd

theorem decimalSplit_form {n : ℕ} (hn : 1 ≤ n) :
    quadraticForm ((decimalSplit n).u : ℝ) ((decimalSplit n).v : ℝ) =
      delta n * (Real.sqrt 5 * (decimalDenominator n : ℝ) - delta n) := by
  have h := stripOnes_form (truncationNumeratorExact n) (decimalDenominator n)
  change quadraticForm ((decimalSplit n).u : ℝ) ((decimalSplit n).v : ℝ) = _ at ⊢
  change quadraticForm ((decimalSplit n).u : ℝ) ((decimalSplit n).v : ℝ) =
    (-1 : ℝ) ^ (decimalSplit n).count *
      quadraticForm (truncationNumeratorExact n : ℝ) (decimalDenominator n : ℝ) at h
  rw [h, (decimalSplit_odd hn).neg_one_pow, ← truncationNumerator_eq_exact, truncation_form]
  ring

end GoldiLochs
