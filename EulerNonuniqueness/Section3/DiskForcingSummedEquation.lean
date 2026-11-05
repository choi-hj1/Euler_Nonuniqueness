import EulerNonuniqueness.Section3.DiskForcingSeriesEquation

namespace EulerNonuniqueness.Paper

noncomputable section

open Set

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance forcingSummedEquationC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem diskForcingPrimitive_tsum_equation_of_weighted_bounds {frequency left right time : ℝ}
    (nonzero : frequency ≠ 0) (amplitude amplitudeDerivative : ℕ → ℝ → ℂ)
    (amplitudeBound derivativeBound : ℕ → ℝ)
    (amplitudeEquation : ∀ degree current, current ∈ Ioo left right →
      HasDerivAt (amplitude degree) (amplitudeDerivative degree current) current)
    (bounds : ∀ degree current, current ∈ Ioo left right →
      ‖amplitude degree current‖ ≤ amplitudeBound degree ∧
        ‖amplitudeDerivative degree current‖ ≤ derivativeBound degree)
    (summableAmplitude : Summable (fun degree => (2 : ℝ) ^ (degree + 1) * amplitudeBound degree))
    (summableDerivative : Summable (fun degree => (2 : ℝ) ^ (degree + 1) * derivativeBound degree))
    (member : time ∈ Ioo left right) :
    HasDerivAt (fun current => ∑' degree, diskForcingPrimitive degree frequency (amplitude degree) current)
      (frequency • diskRotatingDerivative (∑' degree, diskForcingPrimitive degree frequency (amplitude degree) time) +
      (∑' degree, diskForcingTerm degree frequency (amplitude degree) time) +
      (∑' degree, diskForcingPrimitive degree frequency (amplitudeDerivative degree) time)) time := by
  have pointwise (coefficient : ℕ → ℂ) (envelope : ℕ → ℝ)
      (bound : ∀ degree, ‖coefficient degree‖ ≤ envelope degree)
      (summable : Summable (fun degree => (2 : ℝ) ^ (degree + 1) * envelope degree)) :
      Summable (fun degree => (2 : ℝ) ^ (degree + 1) * ‖coefficient degree‖) := by
    exact Summable.of_nonneg_of_le (fun _ => by positivity)
      (fun degree => mul_le_mul_of_nonneg_left (bound degree) (by positivity)) summable
  have weighted := pointwise (fun degree => amplitude degree time) amplitudeBound
    (fun degree => (bounds degree time member).1) summableAmplitude
  have weightedDerivative := pointwise (fun degree => amplitudeDerivative degree time) derivativeBound
    (fun degree => (bounds degree time member).2) summableDerivative
  have equation := diskForcingPrimitive_tsum_hasDerivAt_of_weighted_bounds nonzero amplitude amplitudeDerivative
    amplitudeBound derivativeBound amplitudeEquation bounds summableAmplitude summableDerivative member member
  apply equation.congr_deriv
  exact diskForcingPrimitiveJet_tsum_eq nonzero amplitude amplitudeDerivative time weighted weightedDerivative

end

end EulerNonuniqueness.Paper
