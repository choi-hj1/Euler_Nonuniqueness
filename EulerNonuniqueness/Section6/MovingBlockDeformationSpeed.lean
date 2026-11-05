import EulerNonuniqueness.Section6.MovingBlockVelocityCancellation
import EulerNonuniqueness.Section6.PaperPatchDeformationBounds
import EulerNonuniqueness.Section6.PaperExternalReceiverResidual

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem patchCentroid_relative_velocity_bound_of_boundary_control {count : ℕ}
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
    {gap extent deformation : ℝ} (gapPositive : 0 < gap)
    (control : ∀ patch, BoundaryCloseToCircle scales family.patchMotion time index patch deformation)
    (deformationNonnegative : 0 ≤ deformation) (deformationSmall : deformation ≤ 1 / 16)
    (internalSmall : 8 * scales.radius (index.val + 1) ≤ gap)
    (internalGap : ∀ target source : Fin 4, source ≠ target → gap ≤
      ‖patchCentroid family.patchMotion time index target - patchCentroid family.patchMotion time index source‖)
    (extentBound : ∀ patch, ‖patchCentroid family.patchMotion time index patch -
      quadrupoleCenter family.patchMotion time index‖ ≤ extent)
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
    (centerSeparated : ∀ source ∈ Finset.univ.erase index, ∀ sourcePatch,
      ∀ position ∈ family.patchMotion.domain time source sourcePatch,
      distance source ≤ ‖quadrupoleCenter family.patchMotion time index - position‖)
    (patch : Fin 4) :
    ‖deriv (fun current => patchCentroid family.patchMotion current index patch -
        quadrupoleCenter family.patchMotion current index) time‖ ≤
      2 * (4 * |scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2| / gap +
        3456 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
          (Real.pi * gap ^ 3) +
        (4096 * scales.radius (index.val + 1) ^ 2 * deformation / Real.pi) *
          (∑ source ∈ Finset.univ.erase index, scales.circulation (source.val + 1) / distance source ^ 3) +
        (∑ source ∈ Finset.univ.erase index,
          2 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 2)) * extent) := by
  apply family.patchCentroid_relative_velocity_bound evolution inside amplitudePositive frequencyPositive
    ratioPositive index pathInside material gapPositive internalGap extentBound ?_ ?_ distance
    distancePositive patchSeparated centerSeparated patch
  · intro target
    exact evolution.quadrupoleInternalPatchResidual_bound inside amplitudePositive frequencyPositive ratioPositive
      index target control deformationNonnegative deformationSmall gapPositive internalSmall
      (fun source member => internalGap target source (Finset.mem_erase.mp member).1)
  · intro target
    exact evolution.quadrupoleExternalReceiverResidual_bound inside amplitudePositive frequencyPositive ratioPositive
      index target distance (control target) deformationNonnegative deformationSmall distancePositive sourceBounded
      receiverSmall sourceSmall (centroidSeparated target)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
