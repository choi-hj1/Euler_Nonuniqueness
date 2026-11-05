import EulerNonuniqueness.Section3.MovingSimilarityPhysicalReynolds
import EulerNonuniqueness.Section3.SimilarityPatchAdvection

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper

theorem movingSimilarityBoundary_hasDerivAt
    {center : ℝ → ℂ} {phase : ℝ → ℝ} {shape : ℝ → PeriodicC1HolderHalf}
    {centerVelocity : ℂ} {phaseVelocity radius time : ℝ} {velocity : PeriodicC1HolderHalf}
    (centerEquation : HasDerivAt center centerVelocity time)
    (phaseEquation : HasDerivAt phase phaseVelocity time) (shapeEquation : HasDerivAt shape velocity time)
    (label : ℝ) :
    HasDerivAt (fun parameter => center parameter + radius •
      ((Circle.exp (phase parameter) : ℂ) * (shape parameter).val.1 label))
      (centerVelocity + radius • ((Complex.I * (phaseVelocity : ℂ)) *
        (Circle.exp (phase time) : ℂ) * (shape time).val.1 label +
          (Circle.exp (phase time) : ℂ) * velocity.val.1 label)) time := by
  have derivative := centerEquation.add
    (((hasDerivAt_circle_phase phaseEquation).mul (hasDerivAt_contour_value shapeEquation label)).const_smul radius)
  exact derivative.congr_deriv (by ring)

theorem movingSimilarityDomain_hasDerivAt_spacetime_transport
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
    (functionDerivative : ∀ point, HasFDerivAt function (derivative point) point)
    {source : Vorticity} (sourceIntegrable : Integrable source) (sourceMembership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    (boundaryEquation : ∀ label, HasDerivAt (fun parameter => center parameter + radius •
      ((Circle.exp (phase parameter) : ℂ) * (shape parameter).val.1 label))
      (biotSavart source (center time + radius • ((Circle.exp (phase time) : ℂ) * (shape time).val.1 label))) time) :
    HasDerivAt (fun parameter =>
      ∫ position in similarityPatchDomain (center parameter) radius (Circle.exp (phase parameter))
        (shape parameter) (small parameter), function (parameter, position))
      ((∫ position in similarityPatchDomain (center time) radius (Circle.exp (phase time)) (shape time) (small time),
          derivative (time, position) (1, 0)) +
        ∫ position in similarityPatchDomain (center time) radius (Circle.exp (phase time)) (shape time) (small time),
          derivative (time, position) (0, biotSavart source position)) time := by
  have result := movingSimilarityDomain_hasDerivAt_spacetime_Reynolds center centerVelocity phase phaseVelocity
    radiusPositive centerContinuous centerVelocityContinuous phaseContinuous phaseVelocityContinuous
    centerEquation phaseEquation shape velocity shapeContinuous velocityContinuous small
    time neighborhood neighborhoodPositive equation function derivative functionContinuous derivativeContinuous functionDerivative
  have physicalVelocity (label : ℝ) :
      centerVelocity time + radius • ((Complex.I * (phaseVelocity time : ℂ)) *
        (Circle.exp (phase time) : ℂ) * (shape time).val.1 label +
          (Circle.exp (phase time) : ℂ) * (velocity time).val.1 label) =
        biotSavart source (center time + radius • ((Circle.exp (phase time) : ℂ) * (shape time).val.1 label)) :=
    (movingSimilarityBoundary_hasDerivAt (centerEquation time) (phaseEquation time)
      (equation time (Metric.mem_ball_self neighborhoodPositive)) label).unique (boundaryEquation label)
  let spatialDerivative := fun position : ℂ => (derivative (time, position)).comp (ContinuousLinearMap.inr ℝ ℝ ℂ)
  have advection := integral_similarityPatchDomain_biotSavart_advection (center time) radiusPositive
    (Circle.exp (phase time)) (shape time) (small time) (fun position => function (time, position)) spatialDerivative
    (functionContinuous.comp (continuous_const.prodMk continuous_id))
    ((derivativeContinuous.comp (continuous_const.prodMk continuous_id)).clm_comp continuous_const)
    (fun position => (functionDerivative (time, position)).comp position (hasFDerivAt_prodMk_right time position))
    sourceIntegrable sourceMembership
  apply result.congr_deriv
  congr 1
  change (∫ position in similarityPatchDomain (center time) radius (Circle.exp (phase time))
    (shape time) (small time), derivative (time, position) (0, biotSavart source position)) = _ at advection
  rw [advection]
  apply intervalIntegral.integral_congr
  intro label _
  dsimp only
  rw [physicalVelocity]

end EulerNonuniqueness.Paper
