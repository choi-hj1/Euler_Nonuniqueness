import EulerNonuniqueness.Section3.DiskSpectralQuadraticObservableC11
import EulerNonuniqueness.Section3.DiskSpectralScaledMovingQuadratic
import EulerNonuniqueness.Section3.DiskSpectralMovingSelfDecomposition
import EulerNonuniqueness.General.MovingQuadraticForcingZero

noncomputable section

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete
  chartedThirdBilinearGroup chartedThirdBilinearSpace chartedThirdBilinearComplete

local instance spectralQuadraticObservableEvolutionGroup : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskSpectralMovingQuadraticForcing_zero_actual (state : PeriodicC1HolderHalf) :
    diskSpectralMovingQuadraticForcing state 0 = 0 := by
  let differential := fderiv ℝ diskSpectralMovingQuadraticCorrection (diskRelabelNeutralCLM state)
  have actual := EulerNonuniqueness.General.movingProjectedQuadraticForcing_zero
    diskPhysicalTransverseProjection diskRelabelNeutralCLM (diskSpectralMovingQuadraticCorrection state) differential state
  with_reducible_and_instances
    convert (config := { transparency := .all }) actual using 1
    all_goals first
      | (change (_ : TopologicalSpace PeriodicC1HolderHalf) = _; with_unfolding_all rfl)
      | (simp only [diskSpectralMovingQuadraticForcing, differential])

theorem diskSpectralQuadraticObservable_eventually_self_derivative_identity :
    ∀ᶠ state in 𝓝 (0 : PeriodicC1HolderHalf),
      fderiv ℝ diskSpectralQuadraticObservable state (diskSpectralTubularEulerField state) =
        diskRotatingDerivative (diskSpectralQuadraticObservable state) + diskSpectralMovingSelfRemainder state := by
  filter_upwards [diskSpectralQuadraticObservable_hasLipschitzDerivativeNear_zero.1,
    diskSpectralScaledMovingQuadraticCoordinate_eventually_hasDerivAt 1] with state differentiable equation
  let curve := fun time : ℝ => state + time • diskSpectralTubularEulerField state
  have curveDerivative : HasDerivAt curve (diskSpectralTubularEulerField state) 0 := by
    simpa only [curve, zero_add, one_smul] using
      (hasDerivAt_const (0 : ℝ) state).add ((hasDerivAt_id (0 : ℝ)).smul_const (diskSpectralTubularEulerField state))
  have actual := equation curve 0 0 (by simp only [curve, zero_smul, add_zero])
    (by simpa only [one_smul, add_zero] using curveDerivative)
  have observableDerivative : HasFDerivAt diskSpectralQuadraticObservable
      (fderiv ℝ diskSpectralQuadraticObservable state) state := differentiable.hasFDerivAt
  have derivativeAtCurve : HasFDerivAt diskSpectralQuadraticObservable
      (fderiv ℝ diskSpectralQuadraticObservable state) (curve 0) := by
    simpa only [curve, zero_smul, add_zero] using observableDerivative
  have chain : HasDerivAt (fun time => diskSpectralQuadraticObservable (curve time))
      (fderiv ℝ diskSpectralQuadraticObservable state (diskSpectralTubularEulerField state)) 0 :=
    derivativeAtCurve.comp_hasDerivAt 0 curveDerivative
  have forcingZero := diskSpectralMovingQuadraticForcing_zero_actual state
  have actualObservable : HasDerivAt (fun time => diskSpectralQuadraticObservable (curve time))
      (diskSpectralMovingQuadraticSelfVelocity state) 0 := by
    with_reducible_and_instances
      simpa only [diskSpectralQuadraticObservable, EulerNonuniqueness.General.quadraticCoordinate,
        div_one, one_smul, forcingZero, add_zero] using actual
  have identity := chain.unique actualObservable
  have decomposition := diskSpectralMovingQuadraticSelfVelocity_eq_generator_add_remainder state
  rw [decomposition] at identity
  simpa only [diskSpectralQuadraticObservable, diskSpectralMovingQuadraticCorrection_neutral_parameter,
    curve, zero_smul, add_zero] using identity

theorem diskSpectralQuadraticObservable_exists_forced_evolution_ball :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {curve : ℝ → PeriodicC1HolderHalf} {frequency time : ℝ} (forcing : PeriodicC1HolderHalf),
      ‖curve time‖ ≤ radius →
      HasDerivAt curve (frequency • diskSpectralTubularEulerField (curve time) + forcing) time →
      HasDerivAt (fun current => diskSpectralQuadraticObservable (curve current))
        (frequency • diskRotatingDerivative (diskSpectralQuadraticObservable (curve time)) +
          frequency • diskSpectralMovingSelfRemainder (curve time) +
          fderiv ℝ diskSpectralQuadraticObservable (curve time) forcing) time ∧
      ‖fderiv ℝ diskSpectralQuadraticObservable (curve time) forcing‖ ≤ constant * ‖forcing‖ := by
  obtain ⟨derivativeRadius, derivativePositive, constant, one, derivatives, _⟩ :=
    diskSpectralQuadraticObservable_exists_uniform_derivative_ball
  obtain ⟨identityRadius, identityPositive, identity⟩ := Metric.eventually_nhds_iff.mp
    diskSpectralQuadraticObservable_eventually_self_derivative_identity
  refine ⟨min derivativeRadius (identityRadius / 2), by positivity, constant, one, ?_⟩
  intro curve frequency time forcing nearby equation
  have derivative := derivatives (curve time) (nearby.trans (min_le_left _ _))
  have self := identity (show dist (curve time) 0 < identityRadius by
    rw [dist_zero_right]
    exact (nearby.trans (min_le_right _ _)).trans_lt (by linarith))
  have actual := derivative.1.comp_hasDerivAt time equation
  have velocityIdentity : fderiv ℝ diskSpectralQuadraticObservable (curve time)
      (frequency • diskSpectralTubularEulerField (curve time) + forcing) =
      frequency • diskRotatingDerivative (diskSpectralQuadraticObservable (curve time)) +
        frequency • diskSpectralMovingSelfRemainder (curve time) +
        fderiv ℝ diskSpectralQuadraticObservable (curve time) forcing := by
    rw [map_add, map_smul, self, smul_add]
  exact ⟨actual.congr_deriv velocityIdentity,
    ((fderiv ℝ diskSpectralQuadraticObservable (curve time)).le_opNorm forcing).trans
      (mul_le_mul_of_nonneg_right derivative.2 (norm_nonneg forcing))⟩

end EulerNonuniqueness.Paper
