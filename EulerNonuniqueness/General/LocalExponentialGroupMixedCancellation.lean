import EulerNonuniqueness.General.LocalPeriodicQuadraticMixedCancellation

namespace EulerNonuniqueness.General

noncomputable section

open Filter Set
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem localExponentialGroup_mixed_resonance_zero
    (operator : ℝ → Space →L[ℝ] Space) (bilinear : BilinearEnd Space) (neutral : Space)
    {radius period : ℝ} (radiusPositive : 0 < radius) (periodPositive : 0 < period)
    (continuousOperator : ContinuousOn operator (Icc (-radius) radius))
    (operatorDerivative : HasDerivAt operator ((2 : ℝ) • bilinear neutral) 0)
    (periodic : ∀ᶠ parameter in 𝓝 (0 : ℝ),
      linearExponentialGroup (operator parameter) period = ContinuousLinearMap.id ℝ Space)
    (kernel : operator 0 neutral = 0) (direction : Space) :
    quadraticResonance (linearExponentialGroup (operator 0)) period bilinear neutral direction = 0 := by
  unfold linearExponentialGroup at periodic
  exact localPeriodicExponentialVariation_mixed_resonance_zero operator bilinear neutral
    radiusPositive periodPositive continuousOperator operatorDerivative periodic kernel direction

end

end EulerNonuniqueness.General
