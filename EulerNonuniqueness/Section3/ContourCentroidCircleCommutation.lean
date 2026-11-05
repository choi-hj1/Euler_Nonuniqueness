import EulerNonuniqueness.Section3.ContourCentroidSelfGauge
import EulerNonuniqueness.Section3.DiskChartedEulerField
import EulerNonuniqueness.Section3.DiskForcingModes
import EulerNonuniqueness.General.EquilibriumConstraintDerivative

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance centroidCircleCommutationC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem diskEulerRotatingField_eq_real_combination (data : PeriodicC1HolderHalf) :
    diskEulerRotatingField data =
      (1 : ℝ) • extendedContourVelocity data - (1 / 2 : ℝ) • (Complex.I • data) := by
  unfold diskEulerRotatingField
  rw [one_smul]
  congr 1
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (Complex.I / 2) * data.val.1 label = (1 / 2 : ℝ) • (Complex.I * data.val.1 label)
  rw [Complex.real_smul]
  push_cast
  ring

theorem contourCentroidFunctional_circle_derivative_intertwines :
    (fderiv ℝ contourCentroidFunctional standardCircleBanach).comp diskRotatingDerivative =
      ((-Complex.I / 2) • ContinuousLinearMap.id ℝ ℂ).comp
        (fderiv ℝ contourCentroidFunctional standardCircleBanach) := by
  have small : ‖standardCircleBanach - standardCircleBanach‖ < (1 / 3 : ℝ) := by norm_num
  have centroidJet := (analyticAt_contourCentroidFunctional standardCircleBanach small).differentiableAt.hasFDerivAt
  have jacobianJet := (analyticAt_contourCentroidFunctional standardCircleBanach small).fderiv.differentiableAt.hasFDerivAt
  have positive : (0 : ℝ) < min (1 / 3) (2 / (3 * Real.pi)) := by positivity
  have identity : (fun data : PeriodicC1HolderHalf =>
      fderiv ℝ contourCentroidFunctional data (diskEulerRotatingField data)) =ᶠ[𝓝 standardCircleBanach]
      fun data => ((-Complex.I / 2) • ContinuousLinearMap.id ℝ ℂ) (contourCentroidFunctional data) := by
    filter_upwards [Metric.ball_mem_nhds standardCircleBanach positive] with data nearby
    rw [Metric.mem_ball, dist_eq_norm] at nearby
    rw [diskEulerRotatingField_eq_real_combination]
    have actual := contourCentroidFunctional_derivative_rotating_self data 1 nearby
    simp only [one_smul, one_div] at actual
    simp only [one_smul, one_div]
    rw [actual]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
      Complex.real_smul]
    push_cast
    ring
  with_reducible
    exact EulerNonuniqueness.General.constraint_derivative_intertwines_at_equilibrium
      ((-Complex.I / 2) • ContinuousLinearMap.id ℝ ℂ) centroidJet
      diskEulerRotatingField_hasFDerivAt_circle jacobianJet rfl diskEulerRotatingField_circle identity

end EulerNonuniqueness.Paper
