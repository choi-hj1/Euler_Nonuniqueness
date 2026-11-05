import EulerNonuniqueness.Section3.DiskChartedEulerField
import EulerNonuniqueness.Section3.ContourVelocitySecondFrechet
import EulerNonuniqueness.General.TwiceDifferentiableOperations
import EulerNonuniqueness.General.AnalyticSecondDifferentiability
import EulerNonuniqueness.General.AnalyticCoefficientPullbackSecond
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter Metric
open scoped Topology

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

attribute [local instance] diskChartedEulerRealSpace diskChartedEulerOperatorGroup diskChartedEulerOperatorSpace
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerUniformGroup diskChartedEulerOperatorComplete
local instance chartedSecondContinuousAdd : ContinuousAdd PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousAdd
local instance chartedSecondOperatorUniformAdd : IsUniformAddGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
local instance chartedSecondOperatorContinuousAdd : ContinuousAdd (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  (inferInstance : IsTopologicalAddGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)).toContinuousAdd

theorem diskChartedEulerField_eventually_twice_differentiable :
    ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf),
      DifferentiableAt ℝ diskChartedEulerField increment ∧
      DifferentiableAt ℝ (fderiv ℝ diskChartedEulerField) increment := by
  have threshold : (0 : ℝ) < min 1 (2 / (3 * Real.pi)) := by positivity
  have chartLimit : Tendsto diskStationaryChart (𝓝 (0 : PeriodicC1HolderHalf)) (𝓝 standardCircleBanach) := by
    simpa only [diskStationaryChart_zero] using (diskStationaryChart_analyticAt 0).continuousAt.tendsto
  have nearby := chartLimit.eventually (ball_mem_nhds standardCircleBanach threshold)
  filter_upwards [nearby, diskChartInverseDerivative_analyticAt_zero.eventually_analyticAt] with increment member inverseAnalytic
  have small : ‖diskStationaryChart increment - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
    simpa only [mem_ball, dist_eq_norm (diskStationaryChart increment) standardCircleBanach] using member
  have firstVelocity : ∀ᶠ data in 𝓝 (diskStationaryChart increment),
      DifferentiableAt ℝ extendedContourVelocity data := by
    filter_upwards [isOpen_ball.mem_nhds member] with data inside
    apply differentiableAt_extendedContourVelocity
    simpa only [mem_ball, dist_eq_norm data standardCircleBanach] using inside
  let rotation : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf := c1ProductCLM (c1Constant (Complex.I / 2))
  have firstRotation (data : PeriodicC1HolderHalf) : DifferentiableAt ℝ rotation data := by
    with_reducible
      exact ContinuousLinearMap.differentiableAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
        (F := PeriodicC1HolderHalf) rotation
  have firstField : ∀ᶠ data in 𝓝 (diskStationaryChart increment),
      DifferentiableAt ℝ diskEulerRotatingField data := by
    filter_upwards [firstVelocity] with data actual
    change DifferentiableAt ℝ (fun point => extendedContourVelocity point - rotation point) data
    exact DifferentiableAt.sub (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
      actual (firstRotation data)
  have secondField : DifferentiableAt ℝ (fderiv ℝ diskEulerRotatingField) (diskStationaryChart increment) := by
    change DifferentiableAt ℝ (fderiv ℝ (fun data => extendedContourVelocity data - rotation data)) _
    with_reducible
      exact EulerNonuniqueness.General.differentiableAt_fderiv_sub_linear
        extendedContourVelocity rotation (diskStationaryChart increment) firstVelocity
        (differentiableAt_fderiv_extendedContourVelocity (diskStationaryChart increment) small)
  unfold diskChartedEulerField
  with_reducible
    exact EulerNonuniqueness.General.twice_differentiable_pullback_of_analytic_coefficients
      diskEulerRotatingField diskStationaryChart diskChartInverseDerivative increment firstField secondField
      (diskStationaryChart_analyticAt increment) inverseAnalytic

theorem diskChartedEulerField_second_derivative_symmetric
    (first second : PeriodicC1HolderHalf) :
    fderiv ℝ (fderiv ℝ diskChartedEulerField) 0 first second =
      fderiv ℝ (fderiv ℝ diskChartedEulerField) 0 second first := by
  have actual := diskChartedEulerField_eventually_twice_differentiable
  have firstActual : ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf),
      HasFDerivAt diskChartedEulerField (fderiv ℝ diskChartedEulerField increment) increment :=
    actual.mono (fun _ regular => by
      with_reducible
        exact DifferentiableAt.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
          (F := PeriodicC1HolderHalf) regular.1)
  have secondActual : HasFDerivAt (fderiv ℝ diskChartedEulerField)
      (fderiv ℝ (fderiv ℝ diskChartedEulerField) (0 : PeriodicC1HolderHalf)) 0 :=
    by
      with_reducible
        exact DifferentiableAt.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
          (F := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) actual.self_of_nhds.2
  with_reducible
    exact second_derivative_symmetric_of_eventually_of_real (E := PeriodicC1HolderHalf)
      (F := PeriodicC1HolderHalf) firstActual secondActual first second

end

end EulerNonuniqueness.Paper
