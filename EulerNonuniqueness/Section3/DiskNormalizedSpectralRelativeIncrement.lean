import EulerNonuniqueness.Section3.DiskNormalizedSpectralRelativeError
import EulerNonuniqueness.General.LocalC1LipschitzBounds
import EulerNonuniqueness.General.LocalUniformQuadraticRemainder
import EulerNonuniqueness.General.UniformFirstJetRelativeIncrement

noncomputable section

open Filter Metric Set
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

local instance normalizedRelativeIncrementC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskPhysicalSpectralCoordinate_hasLipschitzDerivativeNear_circle :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear diskPhysicalSpectralCoordinate standardCircleBanach := by
  obtain ⟨radius, positive, constant, one, _, difference⟩ :=
    diskPhysicalSpectralInverseDerivative_exists_uniform_pair_bounds
  have inverseRegular : EulerNonuniqueness.General.LipschitzNear diskPhysicalSpectralInverseDerivative standardCircleBanach := by
    refine ⟨⟨constant, by linarith⟩, closedBall standardCircleBanach radius, closedBall_mem_nhds _ positive, ?_⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro first firstInside final finalInside
    simpa only [dist_eq_norm] using difference first final
      (by simpa only [mem_closedBall, dist_eq_norm] using firstInside)
      (by simpa only [mem_closedBall, dist_eq_norm] using finalInside)
  refine ⟨diskPhysicalSpectralCoordinate_eventually_inverse_derivative.mono (fun _ actual => actual.2.1.differentiableAt), ?_⟩
  apply inverseRegular.congr
  filter_upwards [diskPhysicalSpectralCoordinate_eventually_inverse_derivative] with data actual
  exact actual.2.1.fderiv

theorem diskNormalizedSpectralCoordinate_hasLipschitzDerivativeNear_circle :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear diskNormalizedSpectralCoordinate standardCircleBanach := by
  have inner := EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_contDiffAt_two
    (contourAreaCentroidNormalization_contDiffAt_two standardCircleBanach (by simp))
  have outer : EulerNonuniqueness.General.HasLipschitzDerivativeNear diskPhysicalSpectralCoordinate
      (contourAreaCentroidNormalization standardCircleBanach) := by
    rw [contourAreaCentroidNormalization_circle]
    exact diskPhysicalSpectralCoordinate_hasLipschitzDerivativeNear_circle
  exact EulerNonuniqueness.General.HasLipschitzDerivativeNear.comp
    (outer := diskPhysicalSpectralCoordinate) (inner := contourAreaCentroidNormalization) outer inner

theorem diskNormalizedSpectralCoordinate_exists_relative_shift_ball :
    ∃ radius > 0, ∃ constant ≥ 0,
      ∀ first final firstShift finalShift : PeriodicC1HolderHalf,
      ‖first - standardCircleBanach‖ + (‖firstShift‖ + ‖finalShift‖) ≤ radius →
      ‖final - standardCircleBanach‖ + (‖firstShift‖ + ‖finalShift‖) ≤ radius →
      ‖(diskNormalizedSpectralCoordinate (first - firstShift) - diskNormalizedSpectralCoordinate first) -
        (diskNormalizedSpectralCoordinate (final - finalShift) - diskNormalizedSpectralCoordinate final)‖ ≤
      constant * (‖firstShift - finalShift‖ + ‖first - final‖ * ‖finalShift‖) := by
  let function := fun point : PeriodicC1HolderHalf => diskNormalizedSpectralCoordinate (standardCircleBanach + point)
  have inner : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fun point : PeriodicC1HolderHalf => standardCircleBanach + point) (0 : PeriodicC1HolderHalf) :=
    EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_analyticAt (analyticAt_const.add analyticAt_id)
  have outer : EulerNonuniqueness.General.HasLipschitzDerivativeNear diskNormalizedSpectralCoordinate
      (standardCircleBanach + (0 : PeriodicC1HolderHalf)) := by
    simpa only [add_zero] using diskNormalizedSpectralCoordinate_hasLipschitzDerivativeNear_circle
  have regular : EulerNonuniqueness.General.HasLipschitzDerivativeNear function (0 : PeriodicC1HolderHalf) :=
    EulerNonuniqueness.General.HasLipschitzDerivativeNear.comp
      (outer := diskNormalizedSpectralCoordinate) (inner := fun point => standardCircleBanach + point) outer inner
  obtain ⟨derivativeRadius, derivativePositive, derivativeConstant, derivativeOne, differentiable, derivativeBound, _⟩ :=
    regular.exists_uniform_derivative_ball
  obtain ⟨taylorRadius, taylorPositive, taylorConstant, taylorNonnegative, taylor⟩ :=
    regular.exists_uniform_quadratic_remainder function
  let outerRadius := min derivativeRadius taylorRadius
  let constant := derivativeConstant + taylorConstant
  have positive : 0 < outerRadius := lt_min derivativePositive taylorPositive
  have nonnegative : 0 ≤ constant := by dsimp [constant]; linarith
  have derivativeLe : derivativeConstant ≤ constant := by dsimp [constant]; linarith
  have taylorLe : taylorConstant ≤ constant := by dsimp [constant]; linarith
  have linearBound (point : PeriodicC1HolderHalf) (inside : ‖point‖ ≤ outerRadius) :
      ‖fderiv ℝ function point‖ ≤ constant := by
    exact (derivativeBound point (by simpa only [sub_zero] using inside.trans (min_le_left _ _))).trans derivativeLe
  have taylorBound (point increment : PeriodicC1HolderHalf) (inside : ‖point‖ + ‖increment‖ ≤ outerRadius) :
      ‖EulerNonuniqueness.General.linearJetTaylorError function (fderiv ℝ function) point increment‖ ≤
        constant * ‖increment‖ ^ 2 :=
    (taylor point increment (inside.trans (min_le_right _ _))).trans
      (mul_le_mul_of_nonneg_right taylorLe (sq_nonneg _))
  have actual (point : PeriodicC1HolderHalf) (inside : ‖point‖ < outerRadius) :
      HasFDerivAt function (fderiv ℝ function point) point :=
    (differentiable point (by simpa only [sub_zero] using inside.le.trans (min_le_left _ _))).hasFDerivAt
  refine ⟨outerRadius / 8, by positivity, 6 * constant, by positivity, ?_⟩
  intro first final firstShift finalShift firstInside finalInside
  have relative := EulerNonuniqueness.General.relative_increment_of_uniform_first_jet function (fderiv ℝ function)
    positive nonnegative linearBound taylorBound actual
    (first - standardCircleBanach) (final - standardCircleBanach) (-firstShift) (-finalShift)
    (by simpa only [norm_neg] using firstInside) (by simpa only [norm_neg] using finalInside)
  have baseDifference : (first - standardCircleBanach) - (final - standardCircleBanach) = first - final := by abel
  have shiftDifference : -firstShift - -finalShift = -(firstShift - finalShift) := by abel
  have firstReconstruct : standardCircleBanach + (first - standardCircleBanach) = first := by abel
  have finalReconstruct : standardCircleBanach + (final - standardCircleBanach) = final := by abel
  have firstShiftReconstruct : standardCircleBanach + (first - standardCircleBanach + -firstShift) = first - firstShift := by abel
  have finalShiftReconstruct : standardCircleBanach + (final - standardCircleBanach + -finalShift) = final - finalShift := by abel
  simpa only [function, firstReconstruct, finalReconstruct, firstShiftReconstruct, finalShiftReconstruct,
    baseDifference, shiftDifference, norm_neg] using relative

theorem diskNormalizedSpectralCoordinate_exists_constraints_left_inverse :
    ∃ radius > 0, ∀ state : PeriodicC1HolderHalf, ‖state‖ < radius →
      diskSpectralTubularArea state = Real.pi → contourCentroidFunctional (diskPhysicalSpectralChart state) = 0 →
      diskNormalizedSpectralCoordinate (diskPhysicalSpectralChart state) = state := by
  obtain ⟨radius, positive, contained⟩ := Metric.eventually_nhds_iff.mp diskPhysicalSpectralCoordinate_eventually_left_inverse
  refine ⟨radius, positive, ?_⟩
  intro state nearby area centered
  have inverse := contained (by simpa only [dist_zero_right] using nearby)
  have physicalArea : contourAreaFunctional (diskPhysicalSpectralChart state) = Real.pi := area
  unfold diskNormalizedSpectralCoordinate
  rw [contourAreaCentroidNormalization_fixes_constraints _ physicalArea centered]
  exact inverse

end EulerNonuniqueness.Paper
