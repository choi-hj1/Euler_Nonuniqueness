import EulerNonuniqueness.Section3.MovingSimilarityReynolds

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem movingSimilarityDomain_hasDerivAt_spacetime_Reynolds
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
          derivative (time, position) (1, 0)) +
        ∫ label in (-Real.pi)..Real.pi,
          function (time, center time + radius • ((Circle.exp (phase time) : ℂ) * (shape time).val.1 label)) *
            contourAreaPair (centerVelocity time + radius •
              ((Complex.I * (phaseVelocity time : ℂ)) * (Circle.exp (phase time) : ℂ) * (shape time).val.1 label +
                (Circle.exp (phase time) : ℂ) * (velocity time).val.1 label))
              (radius • ((Circle.exp (phase time) : ℂ) * (shape time).val.2.val.1 label))) time := by
  have result := movingSimilarityDomain_hasDerivAt_spacetime_pullback center centerVelocity phase phaseVelocity
    radiusPositive centerContinuous centerVelocityContinuous phaseContinuous phaseVelocityContinuous
    centerEquation phaseEquation shape velocity shapeContinuous velocityContinuous small
    time neighborhood neighborhoodPositive equation function derivative functionContinuous derivativeContinuous functionDerivative
  let gauge := movingSimilarityGauge center centerVelocity phaseVelocity time
  let spatialDerivative := fun position : ℂ => (derivative (time, position)).comp (ContinuousLinearMap.inr ℝ ℝ ℂ)
  have scalarContinuous : Continuous (fun position : ℂ => function (time, position)) :=
    functionContinuous.comp (continuous_const.prodMk continuous_id)
  have spatialDerivativeContinuous : Continuous spatialDerivative :=
    (derivativeContinuous.comp (continuous_const.prodMk continuous_id)).clm_comp continuous_const
  have scalarDerivative (position : ℂ) : HasFDerivAt (fun position : ℂ => function (time, position))
      (spatialDerivative position) position :=
    (functionDerivative (time, position)).comp position (hasFDerivAt_prodMk_right time position)
  have gaugeContinuous : Continuous gauge := by
    exact continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const))
  let gaugeDerivative : ℂ →L[ℝ] ℂ := (Complex.I * (phaseVelocity time : ℂ)) • ContinuousLinearMap.id ℝ ℂ
  have gaugeEquation (position : ℂ) : HasFDerivAt gauge gaugeDerivative position := by
    exact ((hasFDerivAt_id (𝕜 := ℝ) position).sub_const (center time)).const_mul
      (Complex.I * (phaseVelocity time : ℂ)) |>.const_add (centerVelocity time)
  have gaugeDivergence : contourPlaneTrace gaugeDerivative = 0 := by
    simp [gaugeDerivative, contourPlaneTrace, Complex.mul_re, Complex.mul_im]
  have green := integral_similarityPatchDomain_directional_field (center time) radiusPositive
    (Circle.exp (phase time)) (shape time) (small time) (fun position => function (time, position)) spatialDerivative
    scalarContinuous spatialDerivativeContinuous scalarDerivative gauge (fun _ => gaugeDerivative)
    gaugeContinuous continuous_const gaugeEquation (fun _ => gaugeDivergence)
  have temporalContinuous : Continuous (fun position : ℂ => derivative (time, position) (1, 0)) :=
    (derivativeContinuous.comp (continuous_const.prodMk continuous_id)).clm_apply continuous_const
  have gaugeTermContinuous : Continuous (fun position : ℂ => derivative (time, position) (0, gauge position)) :=
    (derivativeContinuous.comp (continuous_const.prodMk continuous_id)).clm_apply (continuous_const.prodMk gaugeContinuous)
  have temporalIntegrable := similarityPatchDomain_integrable_of_continuous (center time) radiusPositive
    (Circle.exp (phase time)) (shape time) (small time) temporalContinuous
  have gaugeIntegrable := similarityPatchDomain_integrable_of_continuous (center time) radiusPositive
    (Circle.exp (phase time)) (shape time) (small time) gaugeTermContinuous
  have volumeSplit :
      (∫ position in similarityPatchDomain (center time) radius (Circle.exp (phase time)) (shape time) (small time),
        derivative (time, position) (1, gauge position)) =
      (∫ position in similarityPatchDomain (center time) radius (Circle.exp (phase time)) (shape time) (small time),
        derivative (time, position) (1, 0)) +
      ∫ position in similarityPatchDomain (center time) radius (Circle.exp (phase time)) (shape time) (small time),
        derivative (time, position) (0, gauge position) := by
    calc
      _ = ∫ position in similarityPatchDomain (center time) radius (Circle.exp (phase time)) (shape time) (small time),
          derivative (time, position) (1, 0) + derivative (time, position) (0, gauge position) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun position => by dsimp only; rw [← map_add]; simp
      _ = _ := integral_add temporalIntegrable gaugeIntegrable
  change (∫ position in similarityPatchDomain (center time) radius (Circle.exp (phase time)) (shape time) (small time),
      derivative (time, position) (0, gauge position)) = _ at green
  let boundary := fun label : ℝ => center time + radius • ((Circle.exp (phase time) : ℂ) * (shape time).val.1 label)
  let tangent := fun label : ℝ => radius • ((Circle.exp (phase time) : ℂ) * (shape time).val.2.val.1 label)
  let shapeVelocity := fun label : ℝ => radius • ((Circle.exp (phase time) : ℂ) * (velocity time).val.1 label)
  have boundaryContinuous : Continuous boundary :=
    continuous_const.add (continuous_const.smul (continuous_const.mul (shape time).val.1.continuous))
  have tangentContinuous : Continuous tangent :=
    continuous_const.smul (continuous_const.mul (shape time).val.2.val.1.continuous)
  have shapeVelocityContinuous : Continuous shapeVelocity :=
    continuous_const.smul (continuous_const.mul (velocity time).val.1.continuous)
  have gaugeFluxContinuous : Continuous (fun label => function (time, boundary label) * contourAreaPair (gauge (boundary label)) (tangent label)) := by
    dsimp only [contourAreaPair]
    fun_prop
  have shapeFluxContinuous : Continuous (fun label => function (time, boundary label) * contourAreaPair (shapeVelocity label) (tangent label)) := by
    dsimp only [contourAreaPair]
    fun_prop
  apply result.congr_deriv
  change (∫ position in similarityPatchDomain (center time) radius (Circle.exp (phase time)) (shape time) (small time),
      derivative (time, position) (1, gauge position)) + _ = _
  rw [volumeSplit, green, add_assoc,
    ← intervalIntegral.integral_add (gaugeFluxContinuous.intervalIntegrable _ _) (shapeFluxContinuous.intervalIntegrable _ _)]
  congr 1
  apply intervalIntegral.integral_congr
  intro label _
  change function (time, boundary label) * contourAreaPair (gauge (boundary label)) (tangent label) +
    function (time, boundary label) * contourAreaPair (shapeVelocity label) (tangent label) = _
  have identity : gauge (boundary label) + shapeVelocity label = centerVelocity time + radius •
      ((Complex.I * (phaseVelocity time : ℂ)) * (Circle.exp (phase time) : ℂ) * (shape time).val.1 label +
        (Circle.exp (phase time) : ℂ) * (velocity time).val.1 label) := by
    rw [show gauge (boundary label) = centerVelocity time + radius •
        ((Complex.I * (phaseVelocity time : ℂ)) * (Circle.exp (phase time) : ℂ) * (shape time).val.1 label) from
      movingSimilarityGauge_apply center centerVelocity phase phaseVelocity radius time ((shape time).val.1 label)]
    simp only [shapeVelocity, smul_add]
    abel
  dsimp only
  rw [← identity]
  simp only [contourAreaPair_coordinates, Complex.add_re, Complex.add_im]
  ring

end EulerNonuniqueness.Paper
