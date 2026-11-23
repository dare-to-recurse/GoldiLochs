import GoldiLochs.Basic

open Filter
open scoped Topology

/-- An independent spelling of the fixed target against which to check the specification. -/
example :
    GoldiLochs.Target =
      Tendsto (fun n : ℕ =>
        (GoldiLochs.euclidDepth
          (Nat.floor (((1 + Real.sqrt 5) / 2 : ℝ) * ((10 ^ n : ℕ) : ℝ)))
          (10 ^ n) : ℝ) / (n : ℝ))
        atTop (𝓝 (Real.log 10 / (2 * Real.log ((1 + Real.sqrt 5) / 2)) +
          6 * Real.log 2 * Real.log 10 / Real.pi ^ 2)) :=
  rfl

example : (GoldiLochs.depth 0 : ℝ) / (0 : ℝ) = 0 := div_zero _

set_option pp.all true in
#print GoldiLochs.Target
set_option pp.all true in
#print GoldiLochs.target_iff_tailMeanLaw_of_log_scales

#print axioms GoldiLochs.Target
#print axioms GoldiLochs.euclidDepth_zero
#print axioms GoldiLochs.euclidDepth_step
#print axioms GoldiLochs.truncationNumerator_eq_exact
#print axioms GoldiLochs.delta_pos
#print axioms GoldiLochs.delta_lt_one
#print axioms GoldiLochs.nextDigit_lt_ten
#print axioms GoldiLochs.truncationNumerator_succ
#print axioms GoldiLochs.delta_succ
#print axioms GoldiLochs.cf_terminatedAt_iff
#print axioms GoldiLochs.cf_last_convergent
#print axioms GoldiLochs.cf_last_coefficient_ge_two
#print axioms GoldiLochs.euclidDepth_div_gcd
#print axioms GoldiLochs.stripOnes_spec
#print axioms GoldiLochs.stripOnes_fib
#print axioms GoldiLochs.stripOnes_linear
#print axioms GoldiLochs.residual_exact
#print axioms GoldiLochs.residual_coprime
#print axioms GoldiLochs.depth_eq_prefix_add_tail
#print axioms GoldiLochs.decimalSplit_odd
#print axioms GoldiLochs.decimalSplit_form
#print axioms GoldiLochs.residualPhase_eq
#print axioms GoldiLochs.residualPhase_bounds
#print axioms GoldiLochs.split_height_log_bounds
#print axioms GoldiLochs.split_prefix_log_bounds
#print axioms GoldiLochs.prefix_scale
#print axioms GoldiLochs.residual_height_scale
#print axioms GoldiLochs.tailLogSum_eq_log_residualU
#print axioms GoldiLochs.gaussMap_iterate_eq_remainder_ratio
#print axioms GoldiLochs.tailLogSum_eq_gaussIterates
#print axioms GoldiLochs.original_length_eventually_exceptional
#print axioms GoldiLochs.target_iff_tailLaw_of_scales
#print axioms GoldiLochs.tailLaw_iff_tailMeanLaw
#print axioms GoldiLochs.target_iff_tailMeanLaw_of_log_scales
