import EulerNonuniqueness.Section3.MovingMaterialPatchFlux

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem contourAreaPair_add_tangent (velocity tangent : ℂ) (rate : ℝ) :
    contourAreaPair (velocity + rate • tangent) tangent = contourAreaPair velocity tangent := by
  simp only [contourAreaPair_coordinates, Complex.add_re, Complex.add_im, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

namespace MovingMaterialPatch

theorem fluxTransportRate_eq_actual_of_normal_velocity (path : MovingMaterialPatch) (time : ℝ)
    {source : Vorticity} (sourceIntegrable : Integrable source)
    (sourceMembership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    (normalVelocity : ∀ label, contourAreaPair (path.boundaryVelocity time label) (path.boundaryTangent time label) =
      contourAreaPair (biotSavart source (path.boundary time label)) (path.boundaryTangent time label))
    (function : ℝ × ℂ → ℝ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ)
    (functionContinuous : Continuous function) (derivativeContinuous : Continuous derivative)
    (functionDerivative : ∀ point, HasFDerivAt function (derivative point) point) :
    path.fluxTransportRate function derivative time =
      (∫ position in path.domain time, derivative (time, position) (1, 0)) +
        ∫ position in path.domain time, derivative (time, position) (0, biotSavart source position) := by
  let spatialDerivative := fun position : ℂ => (derivative (time, position)).comp (ContinuousLinearMap.inr ℝ ℝ ℂ)
  have advection := integral_similarityPatchDomain_biotSavart_advection (path.center time) path.radius_positive
    (Circle.exp (path.phase time)) (path.shape time) (path.nearby time) (fun position => function (time, position)) spatialDerivative
    (functionContinuous.comp (continuous_const.prodMk continuous_id))
    ((derivativeContinuous.comp (continuous_const.prodMk continuous_id)).clm_comp continuous_const)
    (fun position => (functionDerivative (time, position)).comp position (hasFDerivAt_prodMk_right time position))
    sourceIntegrable sourceMembership
  change (∫ position in path.domain time, derivative (time, position) (0, biotSavart source position)) = _ at advection
  unfold fluxTransportRate
  congr 1
  rw [advection]
  apply intervalIntegral.integral_congr
  intro label _
  change function (time, path.boundary time label) *
    contourAreaPair (path.boundaryVelocity time label) (path.boundaryTangent time label) = _
  rw [normalVelocity]
  rfl

theorem domain_spacetime_integral_hasDerivAt_of_normal_velocity (path : MovingMaterialPatch) {time : ℝ}
    (inside : time ∈ Ioo path.initialTime path.finalTime)
    {source : Vorticity} (sourceIntegrable : Integrable source)
    (sourceMembership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    (normalVelocity : ∀ label, contourAreaPair (path.boundaryVelocity time label) (path.boundaryTangent time label) =
      contourAreaPair (biotSavart source (path.boundary time label)) (path.boundaryTangent time label))
    (function : ℝ × ℂ → ℝ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ)
    (functionContinuous : Continuous function) (derivativeContinuous : Continuous derivative)
    (functionDerivative : ∀ point, HasFDerivAt function (derivative point) point) :
    HasDerivAt (fun parameter => ∫ position in path.domain parameter, function (parameter, position))
      ((∫ position in path.domain time, derivative (time, position) (1, 0)) +
        ∫ position in path.domain time, derivative (time, position) (0, biotSavart source position)) time :=
  (path.domain_spacetime_integral_hasDerivAt_flux inside function derivative functionContinuous derivativeContinuous functionDerivative).congr_deriv
    (path.fluxTransportRate_eq_actual_of_normal_velocity time sourceIntegrable sourceMembership normalVelocity
      function derivative functionContinuous derivativeContinuous functionDerivative)

theorem domain_spacetime_integral_hasDerivAt_of_tangential_relabeling (path : MovingMaterialPatch) {time : ℝ}
    (inside : time ∈ Ioo path.initialTime path.finalTime)
    {source : Vorticity} (sourceIntegrable : Integrable source)
    (sourceMembership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    (rate : ℝ → ℝ)
    (equation : ∀ label, path.boundaryVelocity time label = biotSavart source (path.boundary time label) +
      rate label • path.boundaryTangent time label)
    (function : ℝ × ℂ → ℝ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ)
    (functionContinuous : Continuous function) (derivativeContinuous : Continuous derivative)
    (functionDerivative : ∀ point, HasFDerivAt function (derivative point) point) :
    HasDerivAt (fun parameter => ∫ position in path.domain parameter, function (parameter, position))
      ((∫ position in path.domain time, derivative (time, position) (1, 0)) +
        ∫ position in path.domain time, derivative (time, position) (0, biotSavart source position)) time := by
  apply path.domain_spacetime_integral_hasDerivAt_of_normal_velocity inside sourceIntegrable sourceMembership
    _ function derivative functionContinuous derivativeContinuous functionDerivative
  intro label
  rw [equation, contourAreaPair_add_tangent]

end MovingMaterialPatch

end EulerNonuniqueness.Paper
