import EulerNonuniqueness.Section3.MovingSimilarityPullback

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

def movingSimilarityGauge (center centerVelocity : ℝ → ℂ) (phaseVelocity : ℝ → ℝ)
    (time : ℝ) (position : ℂ) : ℂ :=
  centerVelocity time + (Complex.I * (phaseVelocity time : ℂ)) * (position - center time)

theorem movingSimilarityGauge_apply (center centerVelocity : ℝ → ℂ) (phase phaseVelocity : ℝ → ℝ)
    (radius time : ℝ) (position : ℂ) :
    movingSimilarityGauge center centerVelocity phaseVelocity time
        (center time + radius • ((Circle.exp (phase time) : ℂ) * position)) =
      centerVelocity time + radius •
        ((Complex.I * (phaseVelocity time : ℂ)) * (Circle.exp (phase time) : ℂ) * position) := by
  simp only [movingSimilarityGauge, add_sub_cancel_left, Complex.real_smul]
  ring

theorem movingSimilarityDomain_hasDerivAt_spacetime_pullback
    (center centerVelocity : ℝ → ℂ) (phase phaseVelocity : ℝ → ℝ)
    {radius : ℝ} (radiusPositive : 0 < radius)
    (centerContinuous : Continuous center) (centerVelocityContinuous : Continuous centerVelocity)
    (phaseContinuous : Continuous phase) (phaseVelocityContinuous : Continuous phaseVelocity)
    (centerEquation : ∀ time, HasDerivAt center (centerVelocity time) time)
    (phaseEquation : ∀ time, HasDerivAt phase (phaseVelocity time) time)
    (shape velocity : ℝ → PeriodicC1HolderHalf)
    (shapeContinuous : Continuous shape) (velocityContinuous : Continuous velocity)
    (small : ∀ parameter, ‖shape parameter - standardCircleBanach‖ < 1 / 3)
    (time neighborhood : ℝ) (neighborhoodPositive : 0 < neighborhood)
    (equation : ∀ parameter ∈ Metric.ball time neighborhood, HasDerivAt shape (velocity parameter) parameter)
    (function : ℝ × ℂ → ℝ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ)
    (functionContinuous : Continuous function) (derivativeContinuous : Continuous derivative)
    (functionDerivative : ∀ point, HasFDerivAt function (derivative point) point) :
    HasDerivAt (fun parameter =>
      ∫ position in similarityPatchDomain (center parameter) radius (Circle.exp (phase parameter))
        (shape parameter) (small parameter), function (parameter, position))
      ((∫ position in similarityPatchDomain (center time) radius (Circle.exp (phase time)) (shape time) (small time),
          derivative (time, position) (1, movingSimilarityGauge center centerVelocity phaseVelocity time position)) +
        ∫ label in (-Real.pi)..Real.pi,
          function (time, center time + radius • ((Circle.exp (phase time) : ℂ) * (shape time).val.1 label)) *
            contourAreaPair (radius • ((Circle.exp (phase time) : ℂ) * (velocity time).val.1 label))
              (radius • ((Circle.exp (phase time) : ℂ) * (shape time).val.2.val.1 label))) time := by
  let affine := movingSimilarityMap center phase radius
  let affineDerivative := movingSimilarityDerivative centerVelocity phase phaseVelocity radius
  have affineContinuous : Continuous affine := continuous_movingSimilarityMap center phase radius centerContinuous phaseContinuous
  have affineDerivativeContinuous : Continuous affineDerivative := continuous_movingSimilarityDerivative centerVelocity phase phaseVelocity
    radius centerVelocityContinuous phaseContinuous phaseVelocityContinuous
  let pulledDerivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ := fun point => (derivative (affine point)).comp (affineDerivative point)
  have pulledDerivativeContinuous : Continuous pulledDerivative :=
    (derivativeContinuous.comp affineContinuous).clm_comp affineDerivativeContinuous
  have result := nearCircleInterior_hasDerivAt_spacetime_Reynolds shape velocity shapeContinuous velocityContinuous small
    time neighborhood neighborhoodPositive equation (function ∘ affine) pulledDerivative
    (functionContinuous.comp affineContinuous) pulledDerivativeContinuous
    (fun point => (functionDerivative (affine point)).comp point
      (hasFDerivAt_movingSimilarityMap center centerVelocity phase phaseVelocity radius centerEquation phaseEquation point))
  have multiplied := result.const_mul (radius ^ 2)
  have integralIdentity :
      (fun parameter => ∫ position in similarityPatchDomain (center parameter) radius (Circle.exp (phase parameter))
          (shape parameter) (small parameter), function (parameter, position)) =
        fun parameter => radius ^ 2 * ∫ position in nearCircleInterior (shape parameter) (small parameter),
          (function ∘ affine) (parameter, position) := by
    funext parameter
    exact integral_similarityPatchDomain (center parameter) radiusPositive (Circle.exp (phase parameter))
      (shape parameter) (small parameter) (fun position => function (parameter, position))
  rw [integralIdentity]
  convert multiplied using 1
  rw [mul_add]
  congr 1
  · rw [integral_similarityPatchDomain (center time) radiusPositive (Circle.exp (phase time))
      (shape time) (small time)]
    change radius ^ 2 * _ = radius ^ 2 * _
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun position => by
      simp only [pulledDerivative, ContinuousLinearMap.comp_apply, affineDerivative,
        movingSimilarityDerivative_temporal, movingSimilarityGauge_apply]
      rfl
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro label _
    dsimp only [Function.comp_apply, affine, movingSimilarityMap]
    rw [contourAreaPair_similarity]
    ring

end EulerNonuniqueness.Paper
