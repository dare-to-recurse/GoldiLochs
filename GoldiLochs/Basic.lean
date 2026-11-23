/-
Copyright (c) 2026 Daniel Karlsson. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Daniel Karlsson
-/
module

public import GoldiLochs.Arithmetic
public import GoldiLochs.Backward
public import GoldiLochs.Exceptional
public import GoldiLochs.Gauss
public import GoldiLochs.Phase
public import GoldiLochs.Potential
public import GoldiLochs.Scale
public import GoldiLochs.Tail

/-! # GoldiLochs theorem collection -/

public section

open Filter
open scoped Topology

namespace GoldiLochs

/-- Under the two logarithmic estimates supplied mathematically by Ridout's theorem,
the exact target is equivalent to the mean law for the deterministic finite orbits. -/
theorem target_iff_tailMeanLaw_of_log_scales
    (hdelta : Tendsto (fun n : ℕ => -Real.log (delta n) / (n : ℝ)) atTop (𝓝 0))
    (hgcd : Tendsto (fun n : ℕ => Real.log (commonFactor n : ℝ) / (n : ℝ)) atTop (𝓝 0)) :
    Target ↔ TailMeanLaw :=
  (target_iff_tailLaw_of_scales (prefix_scale hdelta) (residual_height_scale hdelta hgcd)).trans
    tailLaw_iff_tailMeanLaw

/-- The same equivalence, assuming the lower bound on approximation by the original
reduced decimal fractions supplied by a number-theoretic argument. -/
theorem target_iff_tailMeanLaw_of_approximation_bound
    (happrox : ∀ e : ℝ, 0 < e → ∀ᶠ n : ℕ in atTop,
      (reducedDenominator n : ℝ) ^ (-1 - e) ≤ delta n / (decimalDenominator n : ℝ)) :
    Target ↔ TailMeanLaw :=
  let ⟨hdelta, hgcd⟩ := logarithmic_scales_of_approximation_bound happrox
  target_iff_tailMeanLaw_of_log_scales hdelta hgcd

end GoldiLochs
