module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # The decimal truncation and its conjectured Euclidean depth limit -/

@[expose] public section

namespace GoldiLochs

/-- The golden ratio. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

/-- Denominator of the truncation to `n` places after the decimal point. -/
def decimalDenominator (n : ℕ) : ℕ := 10 ^ n

/-- The numerator of the decimal truncation, before cancellation. -/
noncomputable def truncationNumerator (n : ℕ) : ℕ :=
  Nat.floor (phi * (decimalDenominator n : ℝ))

/-- Number of divisions in the Euclidean algorithm, including the initial division. -/
def euclidDepth (a b : ℕ) : ℕ :=
  if h : b = 0 then 0 else 1 + euclidDepth b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)

/-- The complete Euclidean depth of the `n`-place truncation. -/
noncomputable def depth (n : ℕ) : ℕ :=
  euclidDepth (truncationNumerator n) (decimalDenominator n)

/-- The exact candidate for the asymptotic depth per decimal place. -/
noncomputable def proposedConstant : ℝ :=
  Real.log 10 / (2 * Real.log phi) + 6 * Real.log 2 * Real.log 10 / Real.pi ^ 2

/-- The pointwise limit conjecture of `PROMPT.txt`. Division is in `ℝ`,
with value zero at `n = 0`. -/
def Target : Prop :=
  Filter.Tendsto (fun n : ℕ => (depth n : ℝ) / (n : ℝ))
    Filter.atTop (nhds proposedConstant)

end GoldiLochs
