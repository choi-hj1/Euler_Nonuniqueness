import EulerNonuniqueness.Section3.MovingSimilarityTransport

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper

structure MovingMaterialPatch where
  radius : ℝ
  radius_positive : 0 < radius
  initialTime : ℝ
  finalTime : ℝ
  time_order : initialTime < finalTime
  center : ℝ → ℂ
  centerVelocity : ℝ → ℂ
  phase : ℝ → ℝ
  phaseVelocity : ℝ → ℝ
  shape : ℝ → PeriodicC1HolderHalf
  shapeVelocity : ℝ → PeriodicC1HolderHalf
  center_continuous : Continuous center
  centerVelocity_continuous : Continuous centerVelocity
  phase_continuous : Continuous phase
  phaseVelocity_continuous : Continuous phaseVelocity
  shape_continuous : Continuous shape
  shapeVelocity_continuous : Continuous shapeVelocity
  center_equation : ∀ time, HasDerivAt center (centerVelocity time) time
  phase_equation : ∀ time, HasDerivAt phase (phaseVelocity time) time
  shape_equation : ∀ time ∈ Ioo initialTime finalTime, HasDerivAt shape (shapeVelocity time) time
  nearby : ∀ time, ‖shape time - standardCircleBanach‖ < 1 / 3

namespace MovingMaterialPatch

def domain (path : MovingMaterialPatch) (time : ℝ) : Set ℂ :=
  similarityPatchDomain (path.center time) path.radius (Circle.exp (path.phase time))
    (path.shape time) (path.nearby time)

def boundary (path : MovingMaterialPatch) (time label : ℝ) : ℂ :=
  path.center time + path.radius • ((Circle.exp (path.phase time) : ℂ) * (path.shape time).val.1 label)

def boundaryVelocity (path : MovingMaterialPatch) (time label : ℝ) : ℂ :=
  path.centerVelocity time + path.radius •
    ((Complex.I * (path.phaseVelocity time : ℂ)) * (Circle.exp (path.phase time) : ℂ) *
      (path.shape time).val.1 label + (Circle.exp (path.phase time) : ℂ) * (path.shapeVelocity time).val.1 label)

theorem domain_isOpen (path : MovingMaterialPatch) (time : ℝ) : IsOpen (path.domain time) :=
  similarityPatchDomain_isOpen _ path.radius_positive _ _ _

theorem domain_isBounded (path : MovingMaterialPatch) (time : ℝ) : Bornology.IsBounded (path.domain time) :=
  similarityPatchDomain_isBounded _ path.radius_positive _ _ _

theorem domain_frontier (path : MovingMaterialPatch) (time : ℝ) :
    frontier (path.domain time) = range (path.boundary time) :=
  similarityPatchDomain_frontier _ path.radius_positive _ _ _

theorem boundary_hasDerivAt (path : MovingMaterialPatch) {time : ℝ}
    (inside : time ∈ Ioo path.initialTime path.finalTime) (label : ℝ) :
    HasDerivAt (fun parameter => path.boundary parameter label) (path.boundaryVelocity time label) time :=
  movingSimilarityBoundary_hasDerivAt (path.center_equation time) (path.phase_equation time)
    (path.shape_equation time inside) label

theorem integral_continuous_function {value : Type*} [NormedAddCommGroup value] [NormedSpace ℝ value]
    (path : MovingMaterialPatch) (time : ℝ) {function : ℂ → value} (continuous : Continuous function) :
    IntegrableOn function (path.domain time) :=
  (continuous.continuousOn.integrableOn_compact (path.domain_isBounded time).isCompact_closure).mono_set subset_closure

theorem domain_spacetime_integral_hasDerivAt (path : MovingMaterialPatch) {time : ℝ}
    (inside : time ∈ Ioo path.initialTime path.finalTime)
    {source : Vorticity} (sourceIntegrable : Integrable source)
    (sourceMembership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    (material : ∀ label, path.boundaryVelocity time label = biotSavart source (path.boundary time label))
    (function : ℝ × ℂ → ℝ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ)
    (functionContinuous : Continuous function) (derivativeContinuous : Continuous derivative)
    (functionDerivative : ∀ point, HasFDerivAt function (derivative point) point) :
    HasDerivAt (fun parameter => ∫ position in path.domain parameter, function (parameter, position))
      ((∫ position in path.domain time, derivative (time, position) (1, 0)) +
        ∫ position in path.domain time, derivative (time, position) (0, biotSavart source position)) time := by
  let neighborhood := min (time - path.initialTime) (path.finalTime - time)
  have neighborhoodPositive : 0 < neighborhood := lt_min (by linarith [inside.1]) (by linarith [inside.2])
  have ballInside : ∀ parameter ∈ Metric.ball time neighborhood, parameter ∈ Ioo path.initialTime path.finalTime := by
    intro parameter close
    have distance : |parameter - time| < neighborhood := by simpa only [Metric.mem_ball, Real.dist_eq] using close
    have lower := min_le_left (time - path.initialTime) (path.finalTime - time)
    have upper := min_le_right (time - path.initialTime) (path.finalTime - time)
    dsimp only [neighborhood] at distance
    constructor <;> linarith [(abs_lt.mp distance).1, (abs_lt.mp distance).2]
  apply movingSimilarityDomain_hasDerivAt_spacetime_transport path.center path.centerVelocity
    path.phase path.phaseVelocity path.radius_positive path.center_continuous path.centerVelocity_continuous
    path.phase_continuous path.phaseVelocity_continuous path.center_equation path.phase_equation
    path.shape path.shapeVelocity path.shape_continuous path.shapeVelocity_continuous path.nearby
    time neighborhood neighborhoodPositive (fun parameter close => path.shape_equation parameter (ballInside parameter close))
    function derivative functionContinuous derivativeContinuous functionDerivative sourceIntegrable sourceMembership
  intro label
  exact (path.boundary_hasDerivAt inside label).congr_deriv (material label)

theorem domain_integral_hasDerivAt (path : MovingMaterialPatch) {time : ℝ}
    (inside : time ∈ Ioo path.initialTime path.finalTime)
    {source : Vorticity} (sourceIntegrable : Integrable source)
    (sourceMembership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    (material : ∀ label, path.boundaryVelocity time label = biotSavart source (path.boundary time label))
    (function : ℂ → ℝ) (derivative : ℂ → ℂ →L[ℝ] ℝ)
    (functionContinuous : Continuous function) (derivativeContinuous : Continuous derivative)
    (functionDerivative : ∀ position, HasFDerivAt function (derivative position) position) :
    HasDerivAt (fun parameter => ∫ position in path.domain parameter, function position)
      (∫ position in path.domain time, derivative position (biotSavart source position)) time := by
  have result := path.domain_spacetime_integral_hasDerivAt inside sourceIntegrable sourceMembership material
    (fun point => function point.2) (fun point => (derivative point.2).comp (ContinuousLinearMap.snd ℝ ℝ ℂ))
    (functionContinuous.comp continuous_snd) ((derivativeContinuous.comp continuous_snd).clm_comp continuous_const)
    (fun point => (functionDerivative point.2).comp point (ContinuousLinearMap.snd ℝ ℝ ℂ).hasFDerivAt)
  simpa using result

end MovingMaterialPatch

end EulerNonuniqueness.Paper
