import EulerNonuniqueness.Section6.MovingPatchSourceShapeDifference
import EulerNonuniqueness.Section6.ExteriorCoefficientCenterSeries

noncomputable section

open Set Metric MeasureTheory

namespace EulerNonuniqueness.Paper

structure MovingPatchSourceComparison where
  first : MovingMaterialPatch
  second : MovingMaterialPatch
  density : ℝ
  firstReceiver : ℂ
  secondReceiver : ℂ
  receiverRadius : ℝ
  receiverRadius_nonnegative : 0 ≤ receiverRadius
  time : ℝ
  initial : PeriodicC1HolderHalf
  final : PeriodicC1HolderHalf
  firstShape : first.shape time = diskPhysicalSpectralChart initial
  secondShape : second.shape time = diskPhysicalSpectralChart final
  radiusEqual : first.radius = second.radius
  phaseEqual : first.phase time = second.phase time
  firstArea : volume.real (first.domain time) = Real.pi * first.radius ^ 2
  secondArea : volume.real (second.domain time) = Real.pi * second.radius ^ 2

namespace MovingPatchSourceComparison

set_option synthInstance.maxHeartbeats 100000

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

def displacementDifference (comparison : MovingPatchSourceComparison) : ℂ :=
  (comparison.firstReceiver - comparison.first.center comparison.time) -
    (comparison.secondReceiver - comparison.second.center comparison.time)

def spectralDifferenceBudget (comparison : MovingPatchSourceComparison) : ℝ :=
  ‖diskPhysicalTransverseProjection comparison.initial - diskPhysicalTransverseProjection comparison.final‖ +
    (‖diskPhysicalTransverseProjection comparison.initial‖ + ‖diskPhysicalTransverseProjection comparison.final‖) *
      ‖diskNeutralCLM comparison.initial - diskNeutralCLM comparison.final‖

def hybridReceiver (comparison : MovingPatchSourceComparison) : ℂ :=
  comparison.secondReceiver + comparison.first.center comparison.time - comparison.second.center comparison.time

theorem hybridReceiver_displacement (comparison : MovingPatchSourceComparison) :
    comparison.hybridReceiver - comparison.first.center comparison.time =
      comparison.secondReceiver - comparison.second.center comparison.time := by
  unfold hybridReceiver
  abel

theorem firstReceiver_sub_hybridReceiver (comparison : MovingPatchSourceComparison) :
    comparison.firstReceiver - comparison.hybridReceiver = comparison.displacementDifference := by
  unfold hybridReceiver displacementDifference
  abel

theorem spectralDifferenceBudget_nonnegative (comparison : MovingPatchSourceComparison) :
    0 ≤ comparison.spectralDifferenceBudget := by
  unfold spectralDifferenceBudget
  positivity

theorem firstVorticity_integrable (comparison : MovingPatchSourceComparison) :
    Integrable ((comparison.first.domain comparison.time).indicator (fun _ => comparison.density)) :=
  memLp_one_iff_integrable.mp (memLp_indicator_const 1
    (comparison.first.domain_isOpen comparison.time).measurableSet _
    (Or.inr (comparison.first.domain_isBounded comparison.time).measure_lt_top.ne))

theorem firstVorticity_absolute_mass (comparison : MovingPatchSourceComparison) :
    (∫ position, |(comparison.first.domain comparison.time).indicator
      (fun _ => comparison.density) position|) =
        |comparison.density| * Real.pi * comparison.first.radius ^ 2 := by
  have identity : (fun position => |(comparison.first.domain comparison.time).indicator
      (fun _ => comparison.density) position|) =
        (comparison.first.domain comparison.time).indicator (fun _ => |comparison.density|) := by
    funext position
    by_cases member : position ∈ comparison.first.domain comparison.time <;> simp [member]
  rw [identity, integral_indicator (comparison.first.domain_isOpen comparison.time).measurableSet,
    setIntegral_const]
  change volume.real (comparison.first.domain comparison.time) * |comparison.density| = _
  rw [comparison.firstArea]
  ring

theorem firstVorticity_support_separated (comparison : MovingPatchSourceComparison)
    (receiver : ℂ) {distance : ℝ}
    (separated : 2 * comparison.first.radius + distance ≤ ‖receiver - comparison.first.center comparison.time‖) :
    ∀ position ∈ Function.support ((comparison.first.domain comparison.time).indicator (fun _ => comparison.density)),
      distance ≤ ‖receiver - position‖ := by
  intro position nonzero
  have member : position ∈ comparison.first.domain comparison.time := by
    by_contra outside
    exact nonzero (indicator_of_not_mem outside _)
  have radiusBound := comparison.first.domain_subset_ball comparison.time member
  rw [Metric.mem_ball, dist_eq_norm] at radiusBound
  have triangle := norm_add_le (receiver - position) (position - comparison.first.center comparison.time)
  rw [sub_add_sub_cancel] at triangle
  linarith

theorem sourceTaylorCoefficient_center_weighted_term_le (comparison : MovingPatchSourceComparison)
    {distance weight : ℝ} (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (firstSeparated : 2 * comparison.first.radius + distance ≤
      ‖comparison.firstReceiver - comparison.first.center comparison.time‖)
    (secondSeparated : 2 * comparison.first.radius + distance ≤
      ‖comparison.secondReceiver - comparison.second.center comparison.time‖) (power : ℕ) :
    weight ^ (power + 1) *
      ‖comparison.first.sourceTaylorCoefficient comparison.density comparison.firstReceiver comparison.receiverRadius power comparison.time -
        comparison.first.sourceTaylorCoefficient comparison.density comparison.hybridReceiver comparison.receiverRadius power comparison.time‖ ≤
      (4 * weight * ((distance⁻¹ ^ 3 * ‖comparison.displacementDifference‖ *
        (|comparison.density| * Real.pi * comparison.first.radius ^ 2)) / (2 * Real.pi))) *
          (2 * weight * comparison.receiverRadius / distance) ^ power := by
  rw [comparison.first.sourceTaylorCoefficient_eq_vorticityCoefficient,
    comparison.first.sourceTaylorCoefficient_eq_vorticityCoefficient]
  have actual := Section6.exteriorCoefficientCenter_weighted_term_le comparison.firstVorticity_integrable
    comparison.firstReceiver comparison.hybridReceiver comparison.receiverRadius_nonnegative positive weightNonnegative
    (comparison.firstVorticity_support_separated comparison.firstReceiver firstSeparated)
    (comparison.firstVorticity_support_separated comparison.hybridReceiver
      (by simpa only [comparison.hybridReceiver_displacement] using secondSeparated)) power
  simpa only [comparison.firstReceiver_sub_hybridReceiver, comparison.firstVorticity_absolute_mass] using actual

end MovingPatchSourceComparison

end EulerNonuniqueness.Paper
