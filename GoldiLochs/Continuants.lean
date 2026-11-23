module

public import GoldiLochs.Backward
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-! # Digit words and continuants of the finite Euclidean expansion -/

@[expose] public section

namespace GoldiLochs

open scoped Matrix

/-- The quotients in the Euclidean algorithm, including the first quotient. -/
def euclidDigits (a b : ℕ) : List ℕ :=
  if _ : b = 0 then [] else (a / b) :: euclidDigits b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero ‹b ≠ 0›)

@[simp] theorem euclidDigits_zero (a : ℕ) : euclidDigits a 0 = [] := by
  rw [euclidDigits, dite_eq_left rfl]

theorem euclidDigits_step (a : ℕ) {b : ℕ} (hb : 0 < b) :
    euclidDigits a b = (a / b) :: euclidDigits b (a % b) := by
  rw [euclidDigits, dite_eq_right hb.ne']

@[simp] theorem euclidDigits_length (a b : ℕ) : (euclidDigits a b).length = euclidDepth a b := by
  by_cases h : b = 0
  · simp [h]
  · have hb := Nat.pos_of_ne_zero h
    rw [euclidDigits_step a hb, euclidDepth_step a hb, List.length_cons,
      euclidDigits_length b (a % b), Nat.add_comm]
termination_by b
decreasing_by exact Nat.mod_lt _ hb

theorem euclidDigits_pos {a b : ℕ} (hab : b ≤ a) : ∀ c ∈ euclidDigits a b, 0 < c := by
  by_cases h : b = 0
  · simp [h]
  · have hb := Nat.pos_of_ne_zero h
    rw [euclidDigits_step a hb]
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Nat.div_pos hab hb
    · exact euclidDigits_pos (Nat.mod_lt a hb).le c hc
termination_by b
decreasing_by exact Nat.mod_lt _ hb

open GenContFract.IntFractPair in
/-- The quotient list records the integer parts of the canonical continued-fraction stream. -/
theorem euclidDigits_getElem?_eq_stream (a : ℕ) {b : ℕ} (hb : 0 < b) (i : ℕ) :
    (euclidDigits a b)[i]? = (GenContFract.IntFractPair.stream ((a : ℚ) / b) i).map
      (fun p => p.b.toNat) := by
  induction i generalizing a b with
  | zero =>
      simp only [euclidDigits_step a hb, List.getElem?_cons_zero, stream_zero, Option.map_some,
        GenContFract.IntFractPair.of, Rat.floor_natCast_div_natCast, Int.ofNat_ediv_ofNat,
        Int.toNat_natCast]
  | succ i ih =>
      rw [euclidDigits_step a hb, List.getElem?_cons_succ]
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

/-- The symmetric matrix of a continued-fraction digit. -/
def digitMatrix (a : ℕ) : Matrix (Fin 2) (Fin 2) ℕ := !![a, 1; 1, 0]

/-- The ordered product of the matrices of the digits. -/
def continuantMatrix (digits : List ℕ) : Matrix (Fin 2) (Fin 2) ℕ :=
  (digits.map digitMatrix).prod

@[simp] theorem continuantMatrix_nil : continuantMatrix [] = 1 := rfl

theorem continuantMatrix_cons (a : ℕ) (digits : List ℕ) :
    continuantMatrix (a :: digits) = digitMatrix a * continuantMatrix digits := rfl

theorem continuantMatrix_append (left right : List ℕ) :
    continuantMatrix (left ++ right) = continuantMatrix left * continuantMatrix right := by
  rw [continuantMatrix, List.map_append, List.prod_append]
  rfl

/-- The denominator continuant of the digit word. -/
def continuant (digits : List ℕ) : ℕ := continuantMatrix digits 0 0

/-- The numerator of the fraction whose positive-position digits are the given word. -/
def continuantNumerator (digits : List ℕ) : ℕ := continuantMatrix digits 1 0

@[simp] theorem continuant_nil : continuant ([] : List ℕ) = 1 := by
  simp [continuant]

@[simp] theorem continuantNumerator_nil : continuantNumerator ([] : List ℕ) = 0 := by
  simp [continuantNumerator]

theorem continuant_cons (a : ℕ) (digits : List ℕ) :
    continuant (a :: digits) = a * continuant digits + continuantNumerator digits := by
  simp [continuant, continuantNumerator, continuantMatrix_cons, Matrix.mul_apply, Fin.sum_univ_two,
    digitMatrix]

@[simp] theorem continuantNumerator_cons (a : ℕ) (digits : List ℕ) :
    continuantNumerator (a :: digits) = continuant digits := by
  simp [continuant, continuantNumerator, continuantMatrix_cons, Matrix.mul_apply, Fin.sum_univ_two,
    digitMatrix]

theorem continuant_pos {digits : List ℕ} (h : ∀ c ∈ digits, 0 < c) :
    0 < continuant digits := by
  induction digits with
  | nil => simp
  | cons a digits ih =>
      rw [continuant_cons]
      exact Nat.add_pos_left (Nat.mul_pos (h a (by simp)) (ih (fun c hc => h c (by simp [hc])))) _

theorem continuantNumerator_le {digits : List ℕ} (h : ∀ c ∈ digits, 0 < c) :
    continuantNumerator digits ≤ continuant digits := by
  cases digits with
  | nil => simp
  | cons a digits =>
      rw [continuantNumerator_cons, continuant_cons]
      have ha : 1 ≤ a := h a (by simp)
      have hm : 1 * continuant digits ≤ a * continuant digits :=
        Nat.mul_le_mul_right _ ha
      omega

/-- The two first-column entries reconstruct the input up to the common divisor. -/
theorem euclidDigits_continuants (a b : ℕ) :
    a.gcd b * continuant (euclidDigits a b) = a ∧
      a.gcd b * continuantNumerator (euclidDigits a b) = b := by
  by_cases h : b = 0
  · simp [h]
  · have hb := Nat.pos_of_ne_zero h
    obtain ⟨ha, hrem⟩ := euclidDigits_continuants b (a % b)
    rw [gcd_mod_step] at ha hrem
    rw [euclidDigits_step a hb, continuant_cons, continuantNumerator_cons]
    refine ⟨?_, ha⟩
    calc
      a.gcd b * (a / b * continuant (euclidDigits b (a % b)) +
          continuantNumerator (euclidDigits b (a % b))) =
          a / b * (a.gcd b * continuant (euclidDigits b (a % b))) +
            a.gcd b * continuantNumerator (euclidDigits b (a % b)) := by ring
      _ = a := by
        rw [ha, hrem]
        simpa [Nat.add_comm] using Nat.mod_add_div' a b
termination_by b
decreasing_by exact Nat.mod_lt _ hb

theorem continuant_append_mul_le (left right : List ℕ) :
    continuant left * continuant right ≤ continuant (left ++ right) := by
  simp only [continuant, continuantMatrix_append, Matrix.mul_apply, Fin.sum_univ_two]
  exact Nat.le_add_right _ _

/-- Each digit times the continuants on both sides is bounded by the full continuant. -/
theorem digit_continuant_bound (left right : List ℕ) (a : ℕ) :
    a * continuant left * continuant right ≤ continuant (left ++ a :: right) := by
  calc
    a * continuant left * continuant right =
        continuant left * (a * continuant right) := by ring
    _ ≤ continuant left * continuant (a :: right) := by
      apply Nat.mul_le_mul_left
      rw [continuant_cons]
      exact Nat.le_add_right _ _
    _ ≤ continuant (left ++ a :: right) := continuant_append_mul_le _ _

theorem residualDigits_continuants {n : ℕ} (hn : 1 ≤ n) :
    continuant (euclidDigits (residualU n) (residualV n)) = residualU n ∧
      continuantNumerator (euclidDigits (residualU n) (residualV n)) = residualV n := by
  simpa [(residual_coprime hn).gcd_eq_one] using
    euclidDigits_continuants (residualU n) (residualV n)

theorem tail_digit_continuant_bound {n a : ℕ} (hn : 1 ≤ n) (pre post : List ℕ)
    (h : euclidDigits (residualU n) (residualV n) = pre ++ a :: post) :
    a * continuant pre * continuant post ≤ residualU n := by
  rw [← (residualDigits_continuants hn).1, h]
  exact digit_continuant_bound pre post a

theorem continuantMatrix_reverse (digits : List ℕ) :
    continuantMatrix digits.reverse = (continuantMatrix digits)ᵀ := by
  induction digits with
  | nil => simp
  | cons a digits ih =>
      have hsymm : (digitMatrix a)ᵀ = digitMatrix a := by
        ext i j
        fin_cases i <;> fin_cases j <;> rfl
      simp only [List.reverse_cons, continuantMatrix_append, ih, continuantMatrix_cons,
        Matrix.transpose_mul, hsymm, continuantMatrix_nil, mul_one]

@[simp] theorem continuant_reverse (digits : List ℕ) :
    continuant digits.reverse = continuant digits := by
  simp [continuant, continuantMatrix_reverse]

theorem continuantMatrix_determinant (digits : List ℕ) :
    let M := continuantMatrix digits
    (M 0 0 : ℤ) * M 1 1 - (M 0 1 : ℤ) * M 1 0 = (-1 : ℤ) ^ digits.length := by
  induction digits with
  | nil => simp
  | cons a digits ih =>
      dsimp only at ih
      simp [continuantMatrix_cons, Matrix.mul_apply, Fin.sum_univ_two, digitMatrix, pow_succ]
      linear_combination -ih

theorem continuants_coprime (digits : List ℕ) :
    (continuantNumerator digits).Coprime (continuant digits) := by
  let M := continuantMatrix digits
  have hd := continuantMatrix_determinant digits
  change (M 0 0 : ℤ) * M 1 1 - (M 0 1 : ℤ) * M 1 0 = _ at hd
  change (M 1 0).gcd (M 0 0) = 1
  apply Nat.dvd_one.mp
  apply Int.natCast_dvd_natCast.mp
  have hp : ((M 1 0).gcd (M 0 0) : ℤ) ∣ (M 1 0 : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
  have hs : ((M 1 0).gcd (M 0 0) : ℤ) ∣ (M 0 0 : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)
  exact dvd_trans
    (hd ▸ dvd_sub (dvd_mul_of_dvd_left hs _) (dvd_mul_of_dvd_right hp _))
    (isUnit_iff_dvd_one.mp (isUnit_neg_one.pow _))

/-- The cross product with the prefix convergent has magnitude the suffix continuant. -/
theorem continuant_cross (pre post : List ℕ) (a : ℕ) :
    let digits := pre ++ a :: post
    (continuantNumerator digits : ℤ) * continuant pre -
      (continuant digits : ℤ) * continuantNumerator pre =
        (-1 : ℤ) ^ pre.length * continuant post := by
  have hd := continuantMatrix_determinant pre
  dsimp only at hd
  simp only [continuant, continuantNumerator, continuantMatrix_append, Matrix.mul_apply,
    Fin.sum_univ_two, Nat.cast_add, Nat.cast_mul]
  have ht : continuantMatrix (a :: post) 1 0 = continuantMatrix post 0 0 :=
    continuantNumerator_cons a post
  rw [← ht, ← hd]
  ring

/-- The prefix preceding one specified digit is within the reciprocal of
that digit times the square of the prefix denominator. -/
theorem continuant_approximation (pre post : List ℕ) (a : ℕ)
    (h : ∀ c ∈ pre ++ a :: post, 0 < c) :
    let digits := pre ++ a :: post
    let error := |(continuantNumerator digits : ℝ) / continuant digits -
      (continuantNumerator pre : ℝ) / continuant pre|
    0 < error ∧ error ≤ 1 / ((a : ℝ) * (continuant pre : ℝ) ^ 2) := by
  let digits := pre ++ a :: post
  let A : ℝ := a
  let P : ℝ := continuant pre
  let S : ℝ := continuant post
  let D : ℝ := continuant digits
  let C : ℝ := continuantNumerator pre
  let N : ℝ := continuantNumerator digits
  have ha : 0 < A := by
    dsimp [A]
    exact_mod_cast h a (by simp)
  have hp : 0 < P := by
    dsimp [P]
    exact_mod_cast continuant_pos (fun c hc => h c (List.mem_append_left _ hc))
  have hs : 0 < S := by
    dsimp [S]
    exact_mod_cast continuant_pos (fun c hc =>
      h c (List.mem_append_right _ (List.mem_cons_of_mem _ hc)))
  have hd : 0 < D := by
    dsimp [D, digits]
    exact_mod_cast continuant_pos h
  have hcross : N * P - D * C = (-1 : ℝ) ^ pre.length * S := by
    have hcross := congrArg (fun z : ℤ => (z : ℝ)) (continuant_cross pre post a)
    push_cast at hcross
    exact hcross
  have herr : |N / D - C / P| = S / (D * P) := by
    have hdiff : N / D - C / P = (N * P - D * C) / (D * P) := by
      field_simp [hd.ne', hp.ne']
    rw [hdiff, hcross, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos hs, abs_of_pos (mul_pos hd hp)]
  change 0 < |N / D - C / P| ∧ |N / D - C / P| ≤ 1 / (A * P ^ 2)
  rw [herr]
  refine ⟨div_pos hs (mul_pos hd hp), ?_⟩
  apply (div_le_div_iff₀ (mul_pos hd hp) (mul_pos ha (pow_pos hp _))).2
  have hbound : A * P * S ≤ D := by
    dsimp [A, P, S, D, digits]
    exact_mod_cast digit_continuant_bound pre post a
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_right hbound hp.le

theorem euclidDigits_matrix_second_column {a b : ℕ} (hb : 0 < b) :
    let M := continuantMatrix (euclidDigits a b)
    (M 1 1, M 0 1) = penultimatePair a b := by
  rw [euclidDigits_step a hb, continuantMatrix_cons, penultimatePair, dite_eq_right hb.ne']
  by_cases hr : a % b = 0
  · simp [hr, digitMatrix]
  · rw [ite_eq_right hr, ← euclidDigits_matrix_second_column (Nat.pos_of_ne_zero hr)]
    simp [Matrix.mul_apply, Fin.sum_univ_two, digitMatrix]
termination_by b
decreasing_by exact Nat.mod_lt _ hb

/-- Reversing the complete digit word gives the penultimate denominator as its numerator. -/
theorem euclidDigits_reverse_numerator {a b : ℕ} (hb : 0 < b) :
    continuantNumerator (euclidDigits a b).reverse = (penultimatePair a b).2 := by
  rw [continuantNumerator, continuantMatrix_reverse]
  exact congrArg Prod.snd (euclidDigits_matrix_second_column hb)

theorem residualDigits_pos {n : ℕ} (hn : 1 ≤ n) :
    ∀ c ∈ euclidDigits (residualU n) (residualV n), 0 < c := by
  have h := residual_twice_le hn
  exact euclidDigits_pos (by omega)

/-- At the residual ratio the word starts immediately after the zero integer part. -/
theorem residualDigits_getElem?_eq_stream {n : ℕ} (hn : 1 ≤ n) (i : ℕ) :
    (euclidDigits (residualU n) (residualV n))[i]? =
      (GenContFract.IntFractPair.stream ((residualV n : ℚ) / residualU n) (i + 1)).map
        (fun p => p.b.toNat) := by
  have hV := residualV_pos hn
  have hle := residual_twice_le hn
  have hlt : residualV n < residualU n := by omega
  have h := euclidDigits_getElem?_eq_stream (residualV n) (hV.trans hlt) (i + 1)
  simpa [euclidDigits_step (residualV n) (hV.trans hlt), Nat.mod_eq_of_lt hlt] using h

/-- The canonical prefix immediately before a specified tail digit gives a reduced
approximation to the residual ratio. -/
theorem residual_digit_approximation_left {n a : ℕ} (hn : 1 ≤ n) (pre post : List ℕ)
    (h : euclidDigits (residualU n) (residualV n) = pre ++ a :: post) :
    let p := continuantNumerator pre
    let q := continuant pre
    let error := |(residualV n : ℝ) / residualU n - (p : ℝ) / q|
    0 < q ∧ p ≤ q ∧ p.Coprime q ∧
      0 < error ∧ error ≤ 1 / ((a : ℝ) * (q : ℝ) ^ 2) := by
  have hall := residualDigits_pos hn
  rw [h] at hall
  have hp : ∀ c ∈ pre, 0 < c := fun c hc => hall c (List.mem_append_left _ hc)
  have he := continuant_approximation pre post a hall
  dsimp only at he
  rw [← h, (residualDigits_continuants hn).1, (residualDigits_continuants hn).2] at he
  exact ⟨continuant_pos hp, continuantNumerator_le hp, continuants_coprime pre, he⟩

/-- The reversed suffix gives a reduced approximation to the reversed residual ratio,
whose numerator is the penultimate denominator of the original expansion. -/
theorem residual_digit_approximation_right {n a : ℕ} (hn : 1 ≤ n) (pre post : List ℕ)
    (h : euclidDigits (residualU n) (residualV n) = pre ++ a :: post) :
    let p := continuantNumerator post.reverse
    let q := continuant post
    let error := |((penultimatePair (residualU n) (residualV n)).2 : ℝ) / residualU n -
      (p : ℝ) / q|
    0 < q ∧ p ≤ q ∧ p.Coprime q ∧
      0 < error ∧ error ≤ 1 / ((a : ℝ) * (q : ℝ) ^ 2) := by
  have hr : (euclidDigits (residualU n) (residualV n)).reverse =
      post.reverse ++ a :: pre.reverse := by
    simp [h, List.reverse_append, List.reverse_cons, List.append_assoc]
  have hall : ∀ c ∈ post.reverse ++ a :: pre.reverse, 0 < c := by
    simpa [← hr] using residualDigits_pos hn
  have hp : ∀ c ∈ post.reverse, 0 < c := fun c hc => hall c (List.mem_append_left _ hc)
  have he := continuant_approximation post.reverse pre.reverse a hall
  dsimp only at he
  rw [← hr, euclidDigits_reverse_numerator (residualV_pos hn),
    continuant_reverse, (residualDigits_continuants hn).1, continuant_reverse post] at he
  simpa only [continuant_reverse] using
    And.intro (continuant_pos hp)
      (And.intro (continuantNumerator_le hp)
        (And.intro (continuants_coprime post.reverse) he))

end GoldiLochs
