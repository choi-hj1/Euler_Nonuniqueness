import EulerNonuniqueness.Section6.MovingBlockVelocityCancellation
import EulerNonuniqueness.Section6.PaperPatchDeformationBounds
import EulerNonuniqueness.Section6.PaperExternalReceiverResidual

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem patchCentroid_anchor_drift_bound_of_boundary_control {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) {scales : Scales} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count)
    (pathInside : ∀ patch, time ∈ Ioo
      (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ patch label,
      (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
        biotSavart (Paper.patchVorticity scales family.patchMotion time)
          ((family.patch (finProdFinEquiv (index, patch))).boundary time label))
    {gap deformation : ℝ} (gapPositive : 0 < gap)
    (control : ∀ patch, BoundaryCloseToCircle scales family.patchMotion time index patch deformation)
    (deformationNonnegative : 0 ≤ deformation) (deformationSmall : deformation ≤ 1 / 16)
    (internalSmall : 8 * scales.radius (index.val + 1) ≤ gap)
    (internalGap : ∀ target source : Fin 4, source ≠ target → gap ≤
      ‖patchCentroid family.patchMotion time index target - patchCentroid family.patchMotion time index source‖)
    (distance : Fin count → ℝ)
    (distancePositive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (sourceBounded : ∀ source ∈ Finset.univ.erase index, ∀ patch,
      family.patchMotion.domain time source patch ⊆ Metric.closedBall
        (patchCentroid family.patchMotion time source patch) (2 * scales.radius (source.val + 1)))
    (receiverSmall : ∀ source ∈ Finset.univ.erase index, 8 * scales.radius (index.val + 1) ≤ distance source)
    (sourceSmall : ∀ source ∈ Finset.univ.erase index, 4 * scales.radius (source.val + 1) ≤ distance source)
    (centroidSeparated : ∀ target source, source ∈ Finset.univ.erase index → ∀ sourcePatch,
      distance source ≤ ‖patchCentroid family.patchMotion time index target -
        patchCentroid family.patchMotion time source sourcePatch‖)
    (patchSeparated : ∀ patch source, source ∈ Finset.univ.erase index → ∀ sourcePatch,
      ∀ position ∈ family.patchMotion.domain time source sourcePatch,
      distance source ≤ ‖patchCentroid family.patchMotion time index patch - position‖)
    (anchor : ℂ) {extent : ℝ}
    (extentBound : ∀ patch, ‖patchCentroid family.patchMotion time index patch - anchor‖ ≤ extent)
    (anchorSeparated : ∀ source ∈ Finset.univ.erase index, ∀ sourcePatch position,
      position ∈ family.patchMotion.domain time source sourcePatch → distance source ≤ ‖anchor - position‖)
    (patch : Fin 4) :
    ‖deriv (fun current => patchCentroid family.patchMotion current index patch) time -
      biotSavart (externalPatchVorticity scales family.patchMotion time index) anchor‖ ≤
      4 * |scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2| / gap +
        3456 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
          (Real.pi * gap ^ 3) +
        (4096 * scales.radius (index.val + 1) ^ 2 * deformation / Real.pi) *
          (∑ source ∈ Finset.univ.erase index, scales.circulation (source.val + 1) / distance source ^ 3) +
        (∑ source ∈ Finset.univ.erase index,
          2 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 2)) * extent := by
  have derivative := family.patchCentroid_hasDerivAt_point_field evolution inside index patch (pathInside patch) (material patch)
  rw [derivative.deriv]
  have speed := Section6.fourPointField_norm_le
    (coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
    (fun source => patchCentroid family.patchMotion time index source) gapPositive patch (internalGap patch)
  have internalEstimate := evolution.quadrupoleInternalPatchResidual_bound inside amplitudePositive frequencyPositive ratioPositive
    index patch control deformationNonnegative deformationSmall gapPositive internalSmall
    (fun source member => internalGap patch source (Finset.mem_erase.mp member).1)
  have receiverEstimate := evolution.quadrupoleExternalReceiverResidual_bound inside amplitudePositive frequencyPositive ratioPositive
    index patch distance (control patch) deformationNonnegative deformationSmall distancePositive sourceBounded
    receiverSmall sourceSmall (centroidSeparated patch)
  have external := (evolution.externalPatch_biotSavart_bounds inside amplitudePositive frequencyPositive
    ratioPositive index distance distancePositive (patchSeparated patch) anchorSeparated).2
  have nonnegative : 0 ≤ ∑ source ∈ Finset.univ.erase index,
      2 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 2) := by
    apply Finset.sum_nonneg
    intro source _
    have positive := scales.circulation_pos frequencyPositive ratioPositive (source.val + 1)
    positivity
  have externalEstimate := external.trans (mul_le_mul_of_nonneg_left (extentBound patch) nonnegative)
  have identity (point external internal receiver anchor : ℂ) :
      point + external + internal + receiver - anchor = ((point + (external - anchor)) + internal) + receiver := by ring
  rw [identity]
  calc
    _ ≤ ‖Section6.fourPointField
          (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
          (fun source => patchCentroid family.patchMotion time index source) patch‖ +
        ‖biotSavart (externalPatchVorticity scales family.patchMotion time index)
          (patchCentroid family.patchMotion time index patch) -
          biotSavart (externalPatchVorticity scales family.patchMotion time index) anchor‖ +
        ‖quadrupoleInternalPatchResidual scales family.patchMotion time index patch‖ +
        ‖quadrupoleExternalReceiverResidual scales family.patchMotion time index patch‖ :=
      (norm_add_le _ _).trans (add_le_add_right
        ((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)) _)
    _ ≤ _ := by linarith

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily


