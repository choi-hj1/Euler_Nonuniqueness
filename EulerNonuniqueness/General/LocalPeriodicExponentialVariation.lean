import EulerNonuniqueness.General.PeriodicExponentialVariation

namespace EulerNonuniqueness.General

noncomputable section

open Filter Set MeasureTheory
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem localPeriodicExponentialVariation_operator_average_zero
    (operator : ℝ → Space →L[ℝ] Space) (variation : Space →L[ℝ] Space)
    {radius period : ℝ} (radiusPositive : 0 < radius) (periodPositive : 0 < period)
    (continuousOperator : ContinuousOn operator (Icc (-radius) radius))
    (operatorDerivative : HasDerivAt operator variation 0)
    (periodic : ∀ᶠ parameter in 𝓝 (0 : ℝ),
      NormedSpace.exp ℝ (period • operator parameter) = ContinuousLinearMap.id ℝ Space) :
    (∫ time in (0 : ℝ)..period,
      (NormedSpace.exp ℝ ((-time) • operator 0)).comp
        (variation.comp (NormedSpace.exp ℝ (time • operator 0)))) = 0 := by
  let clamp := fun parameter : ℝ => max (-radius) (min radius parameter)
  have clampContinuous : Continuous clamp := continuous_const.max (continuous_const.min continuous_id)
  have clampInside (parameter : ℝ) : clamp parameter ∈ Icc (-radius) radius := by
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have clampZero : clamp 0 = 0 := by
    dsimp only [clamp]
    rw [min_eq_right radiusPositive.le, max_eq_right (by linarith : -radius ≤ 0)]
  have clampIdentity : clamp =ᶠ[𝓝 (0 : ℝ)] id := by
    filter_upwards [Ioo_mem_nhds (by linarith : -radius < 0) radiusPositive] with parameter inside
    dsimp only [clamp, id_eq]
    rw [min_eq_right inside.2.le, max_eq_right inside.1.le]
  have modifiedContinuous : Continuous (fun parameter => operator (clamp parameter)) :=
    continuousOperator.comp_continuous clampContinuous clampInside
  have modifiedDerivative : HasDerivAt (fun parameter => operator (clamp parameter)) variation 0 :=
    operatorDerivative.congr_of_eventuallyEq (clampIdentity.mono (fun _ equality => congrArg operator equality))
  have clampTendsto : Tendsto clamp (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [clampZero] using clampContinuous.tendsto 0
  have modifiedPeriodic : ∀ᶠ parameter in 𝓝 (0 : ℝ),
      NormedSpace.exp ℝ (period • operator (clamp parameter)) = ContinuousLinearMap.id ℝ Space :=
    clampTendsto.eventually periodic
  have actual := periodicExponentialVariation_operator_average_zero
    (fun parameter => operator (clamp parameter)) variation periodPositive modifiedContinuous modifiedDerivative modifiedPeriodic
  simpa only [clampZero] using actual

end

end EulerNonuniqueness.General
