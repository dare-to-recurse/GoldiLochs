module

public import GoldiLochs.Scale
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import GoldiLochs.Phase
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.Fib.Lemmas
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

/-! # Reduced denominators and the arithmetic of the selected residual pair -/

@[expose] public section

open Filter
open scoped Topology

namespace GoldiLochs

/-- The original truncation denominator after cancellation. -/
def reducedDenominator (n : ℕ) : ℕ := decimalDenominator n / commonFactor n

private theorem reducedDenominator_mul_factor (n : ℕ) :
    reducedDenominator n * commonFactor n = decimalDenominator n :=
  Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)

theorem reducedDenominator_pos (n : ℕ) : 0 < reducedDenominator n :=
  Nat.div_gcd_pos_of_pos_right _ (decimalDenominator_pos n)

theorem reducedDenominator_dvd (n : ℕ) : reducedDenominator n ∣ decimalDenominator n :=
  ⟨commonFactor n, (reducedDenominator_mul_factor n).symm⟩

/-- Integrality and nonvanishing of the quadratic form bound the cancellation factor. -/
theorem commonFactor_sq_lt (n : ℕ) :
    (commonFactor n : ℝ) ^ 2 < 3 * (decimalDenominator n : ℝ) := by
  let a := truncationNumeratorExact n
  let q := decimalDenominator n
  let d := commonFactor n
  let p := a / d
  let r := reducedDenominator n
  have ha : (p : ℝ) * d = (a : ℝ) := by
    have h : p * d = a := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
    exact_mod_cast h
  have hqr : (r : ℝ) * d = (q : ℝ) := by
    exact_mod_cast reducedDenominator_mul_factor n
  have hscale : (d : ℝ) ^ 2 * quadraticForm (p : ℝ) (r : ℝ) =
      quadraticForm (a : ℝ) (q : ℝ) := by
    rw [← ha, ← hqr]
    unfold quadraticForm
    ring
  have hq : 0 < (q : ℝ) := by
    change 0 < (decimalDenominator n : ℝ)
    exact_mod_cast decimalDenominator_pos n
  have hform := truncation_form n
  rw [truncationNumerator_eq_exact] at hform
  change quadraticForm (a : ℝ) (q : ℝ) =
    -delta n * (Real.sqrt 5 * (q : ℝ) - delta n) at hform
  have hfac : (q : ℝ) < Real.sqrt 5 * (q : ℝ) - delta n ∧
      Real.sqrt 5 * (q : ℝ) - delta n < 3 * (q : ℝ) := delta_factor_bounds n
  have hneg : quadraticForm (a : ℝ) (q : ℝ) < 0 := by
    rw [hform]
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr (delta_pos n)) (hq.trans hfac.1)
  have hredNeg : quadraticForm (p : ℝ) (r : ℝ) < 0 :=
    neg_of_mul_neg_right (by rwa [hscale]) (sq_nonneg (d : ℝ))
  have hint : (p : ℤ) ^ 2 - (p : ℤ) * (r : ℤ) - (r : ℤ) ^ 2 < 0 := by
    unfold quadraticForm at hredNeg
    exact_mod_cast hredNeg
  have hint' : (p : ℤ) ^ 2 - (p : ℤ) * (r : ℤ) - (r : ℤ) ^ 2 ≤ -1 := by omega
  have hred : quadraticForm (p : ℝ) (r : ℝ) ≤ -1 := by
    unfold quadraticForm
    exact_mod_cast hint'
  have h1 := mul_le_mul_of_nonneg_left hred (sq_nonneg (d : ℝ))
  rw [hscale, hform] at h1
  change (d : ℝ) ^ 2 < 3 * (q : ℝ)
  linarith [mul_lt_mul_of_pos_left hfac.2 (delta_pos n),
    mul_lt_mul_of_pos_right (delta_lt_one n) (show 0 < 3 * (q : ℝ) by positivity)]

theorem reducedDenominator_sq_bound (n : ℕ) :
    (decimalDenominator n : ℝ) < 3 * (reducedDenominator n : ℝ) ^ 2 := by
  have hq : 0 < (decimalDenominator n : ℝ) := by exact_mod_cast decimalDenominator_pos n
  have hr : 0 < (reducedDenominator n : ℝ) := by exact_mod_cast reducedDenominator_pos n
  have hqr : (reducedDenominator n : ℝ) * (commonFactor n : ℝ) = (decimalDenominator n : ℝ) := by
    exact_mod_cast reducedDenominator_mul_factor n
  have h := mul_lt_mul_of_pos_left (commonFactor_sq_lt n) (pow_pos hr 2)
  rw [← mul_pow, hqr] at h
  apply lt_of_mul_lt_mul_left (a := (decimalDenominator n : ℝ)) _ hq.le
  nlinarith only [h]

theorem reducedDenominator_tendsto : Tendsto reducedDenominator atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have hq : Tendsto decimalDenominator atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (10 : ℕ))
  filter_upwards [tendsto_atTop.1 hq (3 * b ^ 2)] with n hn
  have hcast : 3 * (b : ℝ) ^ 2 ≤ (decimalDenominator n : ℝ) := by exact_mod_cast hn
  have hsq := hcast.trans_lt (reducedDenominator_sq_bound n)
  exact_mod_cast (show (b : ℝ) ≤ (reducedDenominator n : ℝ) by
    by_contra! h
    have hle := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (reducedDenominator n)) h.le 2
    linarith)

/-- The logarithmic consequence of a lower bound for approximation by the reduced
decimal fractions. The approximation bound itself is the external Diophantine input. -/
theorem logarithmic_scales_of_approximation_bound
    (happrox : ∀ e : ℝ, 0 < e → ∀ᶠ n : ℕ in atTop,
      (reducedDenominator n : ℝ) ^ (-1 - e) ≤ delta n / (decimalDenominator n : ℝ)) :
    Tendsto (fun n : ℕ => -Real.log (delta n) / (n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => Real.log (commonFactor n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hd_nonneg (n : ℕ) : 0 ≤ Real.log (commonFactor n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast commonFactor_pos n)
  have he_nonneg (n : ℕ) : 0 ≤ -Real.log (delta n) :=
    neg_nonneg.mpr (Real.log_nonpos (delta_pos n).le (delta_lt_one n).le)
  have hlog10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hbound (c : ℝ) (hc : 0 < c) :
      ∀ᶠ n : ℕ in atTop, -Real.log (delta n) / (n : ℝ) < c ∧
        Real.log (commonFactor n : ℝ) / (n : ℝ) < c := by
    let e := (c / 2) / Real.log 10
    have he : 0 < e := div_pos (by linarith) hlog10
    have heq : e * Real.log 10 = c / 2 := div_mul_cancel₀ _ hlog10.ne'
    filter_upwards [happrox e he, eventually_ge_atTop 1] with n hn hn1
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hQ : 0 < (decimalDenominator n : ℝ) := by exact_mod_cast decimalDenominator_pos n
    have hq : 0 < (reducedDenominator n : ℝ) := by exact_mod_cast reducedDenominator_pos n
    have hd : 0 < (commonFactor n : ℝ) := by exact_mod_cast commonFactor_pos n
    have hmul : (reducedDenominator n : ℝ) * (commonFactor n : ℝ) =
        (decimalDenominator n : ℝ) := by exact_mod_cast reducedDenominator_mul_factor n
    have hlogs := congrArg Real.log hmul
    rw [Real.log_mul hq.ne' hd.ne', log_decimalDenominator] at hlogs
    have hineq := Real.log_le_log (Real.rpow_pos_of_pos hq _) hn
    rw [Real.log_rpow hq, Real.log_div (delta_pos n).ne' hQ.ne', log_decimalDenominator] at hineq
    have htotal :
        -Real.log (delta n) + (1 + e) * Real.log (commonFactor n : ℝ) ≤ (c / 2) * n := by
      linear_combination hineq + (1 + e) * hlogs + (n : ℝ) * heq
    have hlogd := hd_nonneg n
    have hloge := he_nonneg n
    have hprod := mul_nonneg he.le hlogd
    have hc' := mul_pos (show 0 < c / 2 by linarith) hn0
    constructor <;> apply (div_lt_iff₀ hn0).2 <;> linarith
  constructor <;> apply tendsto_order.2 <;> constructor
  · intro a ha
    exact Eventually.of_forall (fun n =>
      ha.trans_le (div_nonneg (he_nonneg n) (Nat.cast_nonneg n)))
  · intro a ha
    exact (hbound a ha).mono (fun _ hn => hn.1)
  · intro a ha
    exact Eventually.of_forall (fun n =>
      ha.trans_le (div_nonneg (hd_nonneg n) (Nat.cast_nonneg n)))
  · intro a ha
    exact (hbound a ha).mono (fun _ hn => hn.2)

theorem stripOnes_fib_denominator (a b : ℕ) (hk : 0 < (stripOnes a b).count) :
    b = Nat.fib (stripOnes a b).count * (stripOnes a b).u +
      Nat.fib ((stripOnes a b).count - 1) * (stripOnes a b).v := by
  let s := stripOnes a b
  obtain ⟨ha, hab⟩ := stripOnes_fib a b
  change a = Nat.fib (s.count + 1) * s.u + Nat.fib s.count * s.v at ha
  change a + b = Nat.fib (s.count + 2) * s.u + Nat.fib (s.count + 1) * s.v at hab
  change b = Nat.fib s.count * s.u + Nat.fib (s.count - 1) * s.v
  have hprev : s.count - 1 + 1 = s.count := by
    change 0 < s.count at hk
    omega
  have hrec : Nat.fib (s.count + 1) = Nat.fib (s.count - 1) + Nat.fib s.count := by
    have h := Nat.fib_add_two (n := s.count - 1)
    change Nat.fib (s.count - 1 + 1 + 1) =
      Nat.fib (s.count - 1) + Nat.fib (s.count - 1 + 1) at h
    rw [hprev] at h
    exact h
  simp only [Nat.fib_add_two (n := s.count), hrec, add_mul] at ha hab
  omega

/-- A linear equation characterizing the residual V before cancellation. -/
theorem decimalSplit_v_linear {n : ℕ} (hn : 1 ≤ n) :
    Nat.fib (decimalSplit n).count * truncationNumeratorExact n =
      (decimalSplit n).v + Nat.fib ((decimalSplit n).count + 1) * decimalDenominator n := by
  let a := truncationNumeratorExact n
  let q := decimalDenominator n
  let s := decimalSplit n
  have hodd : Odd s.count := decimalSplit_odd hn
  have hk : 0 < s.count := by
    obtain ⟨m, hm⟩ := hodd
    omega
  have ha : a = Nat.fib (s.count + 1) * s.u + Nat.fib s.count * s.v :=
    (stripOnes_fib a q).1
  have hq : q = Nat.fib s.count * s.u + Nat.fib (s.count - 1) * s.v :=
    stripOnes_fib_denominator a q hk
  have ha' : (a : ℤ) = (Nat.fib (s.count + 1) : ℤ) * s.u + (Nat.fib s.count : ℤ) * s.v := by
    exact_mod_cast ha
  have hq' : (q : ℤ) = (Nat.fib s.count : ℤ) * s.u + (Nat.fib (s.count - 1) : ℤ) * s.v := by
    exact_mod_cast hq
  have hc := Int.fib_succ_mul_fib_pred_sub_fib_sq (s.count : ℤ)
  have hprev : (s.count : ℤ) - 1 = ((s.count - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ s.count), Nat.cast_one]
  rw [← Nat.cast_add_one, hprev, Int.fib_natCast,
    Int.fib_natCast, Int.fib_natCast, Int.natAbs_natCast, hodd.neg_one_pow] at hc
  have h : (Nat.fib s.count : ℤ) * a =
      (s.v : ℤ) + (Nat.fib (s.count + 1) : ℤ) * q := by
    linear_combination (Nat.fib s.count : ℤ) * ha' -
      (Nat.fib (s.count + 1) : ℤ) * hq' - (s.v : ℤ) * hc
  change Nat.fib s.count * a = s.v + Nat.fib (s.count + 1) * q
  exact_mod_cast h

/-- Cassini inversion restricts the residual integer to one residue class. -/
theorem decimalSplit_v_congruence {n : ℕ} (hn : 1 ≤ n) :
    Nat.fib (decimalSplit n).count ∣
      (decimalSplit n).v + Nat.fib ((decimalSplit n).count + 1) * decimalDenominator n :=
  ⟨truncationNumeratorExact n, (decimalSplit_v_linear hn).symm⟩

/-- The congruence for the residual integer has at most six candidates in this range. -/
theorem decimalSplit_v_lt_six_fib {n : ℕ} (hn : 1 ≤ n) :
    (decimalSplit n).v < 6 * Nat.fib (decimalSplit n).count := by
  let k := (decimalSplit n).count
  let v : ℝ := (decimalSplit n).v
  let f : ℝ := Nat.fib k
  let q : ℝ := decimalDenominator n
  let p : ℝ := phi ^ k
  have hodd : Odd k := decimalSplit_odd hn
  have hk : 0 < k := by obtain ⟨m, hm⟩ := hodd; omega
  have hf : 0 < f := by
    change 0 < (Nat.fib k : ℝ)
    exact_mod_cast Nat.fib_pos.mpr hk
  have hphi : 1 < phi := Real.one_lt_goldenRatio
  have hp : 0 < p := pow_pos (by linarith) k
  have hp4 : 0 < phi ^ 4 := pow_pos (by linarith) 4
  have hpow4 : phi ^ 4 < 7 := by
    have hphi' : phi < 5 / 3 := by
      have h : Real.sqrt 5 < 7 / 3 :=
        (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
      unfold phi
      linarith
    calc
      phi ^ 4 = (phi + 1) ^ 2 := by rw [← phi_sq]; ring
      _ = 3 * phi + 2 := by nlinarith [phi_sq]
      _ < 7 := by linarith
  have hsqrt : 0 < Real.sqrt 5 := by positivity
  have he := delta_pos n
  have hq0 : 0 < (decimalDenominator n : ℝ) := by exact_mod_cast decimalDenominator_pos n
  have hQ : 0 < Real.sqrt 5 * q - delta n := hq0.trans (delta_factor_bounds n).1
  have hconj : Real.goldenConj ^ k = -p⁻¹ := by
    have h : Real.goldenConj = -phi⁻¹ := by rw [show phi = Real.goldenRatio by rfl,
      Real.inv_goldenRatio, neg_neg]
    rw [h, hodd.neg_pow, inv_pow]
  have hbinet : f * Real.sqrt 5 = p + p⁻¹ := by
    change (Nat.fib k : ℝ) * Real.sqrt 5 = _
    rw [Real.coe_fib_eq, hconj, div_mul_cancel₀ _ hsqrt.ne']
    change p - -p⁻¹ = p + p⁻¹
    rw [sub_neg_eq_add]
  have hsucc : (Nat.fib (k + 1) : ℝ) - phi * f = -p⁻¹ := by
    rw [← hconj]
    exact Real.fib_succ_sub_goldenRatio_mul_fib k
  have hv : v + f * delta n = q * p⁻¹ := by
    have hnat := decimalSplit_v_linear hn
    have hcast : f * (truncationNumeratorExact n : ℝ) =
        v + (Nat.fib (k + 1) : ℝ) * q := by
      change (Nat.fib k : ℝ) * (truncationNumeratorExact n : ℝ) =
        ((decimalSplit n).v : ℝ) + (Nat.fib (k + 1) : ℝ) * (decimalDenominator n : ℝ)
      exact_mod_cast hnat
    rw [← truncationNumerator_eq_exact] at hcast
    have hd : delta n = phi * q - (truncationNumerator n : ℝ) := rfl
    linear_combination f * hd - hcast - q * hsucc
  have hz := (residualPhase_bounds hn).1
  rw [residualPhase_eq hn, two_mul, pow_add] at hz
  change (phi ^ 4)⁻¹ ≤ p * p * delta n / (Real.sqrt 5 * q - delta n) at hz
  have hcross : Real.sqrt 5 * q - delta n ≤ phi ^ 4 * (p * p * delta n) := by
    have h := (le_div_iff₀ hQ).1 hz
    rw [inv_mul_eq_div] at h
    exact (div_le_iff₀ hp4).1 h |>.trans_eq (mul_comm _ _)
  have hquot :
      (v + f * delta n) * Real.sqrt 5 ≤ phi ^ 4 * delta n * (f * Real.sqrt 5) := by
    rw [hv, hbinet]
    have h := mul_le_mul_of_nonneg_right hcross (inv_nonneg.mpr hp.le)
    have h1 := mul_inv_cancel₀ hp.ne'
    have h2 := mul_nonneg (sub_nonneg.mpr (one_le_pow₀ (n := 4) hphi.le))
      (mul_nonneg he.le (inv_nonneg.mpr hp.le))
    nlinarith only [h, congrArg (fun x : ℝ => phi ^ 4 * p * delta n * x) h1, h2]
  have hvle : v + f * delta n ≤ phi ^ 4 * delta n * f := by
    apply le_of_mul_le_mul_right _ hsqrt
    simpa only [mul_assoc] using hquot
  have hδ := delta_lt_one n
  have hfactor : 0 < (phi ^ 4 - 1) * f :=
    mul_pos (sub_pos.mpr (one_lt_pow₀ hphi (by decide))) hf
  have hlt : v < 6 * f := calc
    v ≤ ((phi ^ 4 - 1) * f) * delta n := by linarith only [hvle]
    _ < ((phi ^ 4 - 1) * f) * 1 := mul_lt_mul_of_pos_left hδ hfactor
    _ < 6 * f := by
      rw [mul_one]
      exact mul_lt_mul_of_pos_right (by linarith) hf
  change ((decimalSplit n).v : ℝ) < 6 * (Nat.fib k : ℝ) at hlt
  exact_mod_cast hlt

end GoldiLochs
