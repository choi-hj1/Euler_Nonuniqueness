import EulerNonuniqueness.Section3.MovingMaterialPatchContinuity

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.MovingMaterialPatch

def boundaryTangent (path : MovingMaterialPatch) (time label : ℝ) : ℂ :=
  path.radius • ((Circle.exp (path.phase time) : ℂ) * (path.shape time).val.2.val.1 label)

theorem continuous_boundary (path : MovingMaterialPatch) : Continuous (Function.uncurry path.boundary) := by
  have curve := continuous_contour_value_joint path.shape path.shape_continuous
  exact (path.center_continuous.comp continuous_fst).add (continuous_const.smul
    (((continuous_subtype_val.comp (Circle.exp.continuous.comp path.phase_continuous)).comp continuous_fst).mul curve))

theorem continuous_boundaryVelocity (path : MovingMaterialPatch) :
    Continuous (Function.uncurry path.boundaryVelocity) := by
  have curve := continuous_contour_value_joint path.shape path.shape_continuous
  have velocity := continuous_contour_value_joint path.shapeVelocity path.shapeVelocity_continuous
  have phaseContinuous : Continuous (fun point : ℝ × ℝ => (Circle.exp (path.phase point.1) : ℂ)) :=
    (continuous_subtype_val.comp (Circle.exp.continuous.comp path.phase_continuous)).comp continuous_fst
  exact (path.centerVelocity_continuous.comp continuous_fst).add (continuous_const.smul
    ((((continuous_const.mul (Complex.continuous_ofReal.comp
      (path.phaseVelocity_continuous.comp continuous_fst))).mul phaseContinuous).mul curve).add
      (phaseContinuous.mul velocity)))

theorem continuous_boundaryTangent (path : MovingMaterialPatch) :
    Continuous (Function.uncurry path.boundaryTangent) := by
  exact continuous_const.smul
    (((continuous_subtype_val.comp (Circle.exp.continuous.comp path.phase_continuous)).comp continuous_fst).mul
      (continuous_contour_tangent_joint path.shape path.shape_continuous))

def fluxTransportRate (path : MovingMaterialPatch) (function : ℝ × ℂ → ℝ)
    (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ) (time : ℝ) : ℝ :=
  (∫ position in path.domain time, derivative (time, position) (1, 0)) +
    ∫ label in (-Real.pi)..Real.pi, function (time, path.boundary time label) *
      contourAreaPair (path.boundaryVelocity time label) (path.boundaryTangent time label)

theorem continuous_fluxTransportRate (path : MovingMaterialPatch)
    (function : ℝ × ℂ → ℝ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ)
    (functionContinuous : Continuous function) (derivativeContinuous : Continuous derivative) :
    Continuous (path.fluxTransportRate function derivative) := by
  have temporal := path.continuous_domain_spacetime_integral
    (fun point => derivative point (1, 0)) (derivativeContinuous.clm_apply continuous_const)
  have boundaryIntegrand : Continuous (fun point : ℝ × ℝ => function (point.1, path.boundary point.1 point.2) *
      contourAreaPair (path.boundaryVelocity point.1 point.2) (path.boundaryTangent point.1 point.2)) :=
    (functionContinuous.comp (continuous_fst.prodMk path.continuous_boundary)).mul
      (continuous_contourAreaPair.comp (path.continuous_boundaryVelocity.prodMk path.continuous_boundaryTangent))
  exact temporal.add (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) boundaryIntegrand continuous_const)

theorem domain_spacetime_integral_hasDerivAt_flux (path : MovingMaterialPatch) {time : ℝ}
    (inside : time ∈ Ioo path.initialTime path.finalTime)
    (function : ℝ × ℂ → ℝ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ)
    (functionContinuous : Continuous function) (derivativeContinuous : Continuous derivative)
    (functionDerivative : ∀ point, HasFDerivAt function (derivative point) point) :
    HasDerivAt (fun parameter => ∫ position in path.domain parameter, function (parameter, position))
      (path.fluxTransportRate function derivative time) time := by
  let neighborhood := min (time - path.initialTime) (path.finalTime - time)
  have neighborhoodPositive : 0 < neighborhood := lt_min (by linarith [inside.1]) (by linarith [inside.2])
  have ballInside : ∀ parameter ∈ Metric.ball time neighborhood, parameter ∈ Ioo path.initialTime path.finalTime := by
    intro parameter close
    have distance : |parameter - time| < neighborhood := by simpa only [Metric.mem_ball, Real.dist_eq] using close
    have lower := min_le_left (time - path.initialTime) (path.finalTime - time)
    have upper := min_le_right (time - path.initialTime) (path.finalTime - time)
    dsimp only [neighborhood] at distance
    constructor <;> linarith [(abs_lt.mp distance).1, (abs_lt.mp distance).2]
  exact movingSimilarityDomain_hasDerivAt_spacetime_Reynolds path.center path.centerVelocity path.phase path.phaseVelocity
    path.radius_positive path.center_continuous path.centerVelocity_continuous path.phase_continuous path.phaseVelocity_continuous
    path.center_equation path.phase_equation path.shape path.shapeVelocity path.shape_continuous path.shapeVelocity_continuous
    path.nearby time neighborhood neighborhoodPositive (fun parameter close => path.shape_equation parameter (ballInside parameter close))
    function derivative functionContinuous derivativeContinuous functionDerivative

theorem fluxTransportRate_eq_actual (path : MovingMaterialPatch) {time : ℝ}
    (inside : time ∈ Ioo path.initialTime path.finalTime)
    {source : Vorticity} (sourceIntegrable : Integrable source)
    (sourceMembership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    (material : ∀ label, path.boundaryVelocity time label = biotSavart source (path.boundary time label))
    (function : ℝ × ℂ → ℝ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ)
    (functionContinuous : Continuous function) (derivativeContinuous : Continuous derivative)
    (functionDerivative : ∀ point, HasFDerivAt function (derivative point) point) :
    path.fluxTransportRate function derivative time =
      (∫ position in path.domain time, derivative (time, position) (1, 0)) +
        ∫ position in path.domain time, derivative (time, position) (0, biotSavart source position) :=
  (path.domain_spacetime_integral_hasDerivAt_flux inside function derivative functionContinuous derivativeContinuous
    functionDerivative).unique (path.domain_spacetime_integral_hasDerivAt inside sourceIntegrable sourceMembership material
      function derivative functionContinuous derivativeContinuous functionDerivative)

theorem integral_fluxTransportRate_eq_sub (path : MovingMaterialPatch) {horizon : ℝ}
    (nonnegative : 0 ≤ horizon) (initialInside : path.initialTime < 0) (finalInside : horizon < path.finalTime)
    (function : ℝ × ℂ → ℝ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ)
    (functionContinuous : Continuous function) (derivativeContinuous : Continuous derivative)
    (functionDerivative : ∀ point, HasFDerivAt function (derivative point) point) :
    (∫ time in (0 : ℝ)..horizon, path.fluxTransportRate function derivative time) =
      (∫ position in path.domain horizon, function (horizon, position)) -
        ∫ position in path.domain 0, function (0, position) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro time member
    rw [uIcc_of_le nonnegative] at member
    exact path.domain_spacetime_integral_hasDerivAt_flux ⟨initialInside.trans_le member.1, member.2.trans_lt finalInside⟩
      function derivative functionContinuous derivativeContinuous functionDerivative
  · exact (path.continuous_fluxTransportRate function derivative functionContinuous derivativeContinuous).intervalIntegrable 0 horizon

end EulerNonuniqueness.Paper.MovingMaterialPatch
