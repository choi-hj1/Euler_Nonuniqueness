import EulerNonuniqueness.General.LinearExponentialGroup
import EulerNonuniqueness.General.PeriodicGeneratorAverage

namespace EulerNonuniqueness.General

noncomputable section

open Filter MeasureTheory
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem periodicExponentialVariation_operator_average_zero
    (operator : ℝ → Space →L[ℝ] Space) (variation : Space →L[ℝ] Space)
    {period : ℝ} (periodPositive : 0 < period) (continuousOperator : Continuous operator)
    (operatorDerivative : HasDerivAt operator variation 0)
    (periodic : ∀ᶠ parameter in 𝓝 (0 : ℝ),
      NormedSpace.exp ℝ (period • operator parameter) = ContinuousLinearMap.id ℝ Space) :
    (∫ time in (0 : ℝ)..period,
      (NormedSpace.exp ℝ ((-time) • operator 0)).comp
        (variation.comp (NormedSpace.exp ℝ (time • operator 0)))) = 0 := by
  exact periodicGeneratorVariation_operator_average_zero
    (fun parameter => linearExponentialGroup (operator parameter)) operator variation periodPositive
    (linearExponentialGroup_continuous_family continuousOperator)
    (fun parameter => linearExponentialGroup_zero (operator parameter))
    (fun parameter => linearExponentialGroup_add (operator parameter))
    (fun parameter => linearExponentialGroup_hasDerivAt_left (operator parameter))
    operatorDerivative periodic

end

end EulerNonuniqueness.General
