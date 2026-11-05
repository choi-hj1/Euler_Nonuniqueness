import EulerNonuniqueness.Section3.FiniteMovingPatchEvolution
import EulerNonuniqueness.Section6.PaperPatchCentroidAlgebra

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

variable {count : ℕ}

theorem patchCentroid_hasDerivAt (family : FiniteMovingPatchFamily (count * 4))
    {scales : Scales} {horizon time : ℝ} (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (inside : time ∈ Icc 0 horizon) (index : Fin count) (patch : Fin 4)
    (pathInside : time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ label, (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
      biotSavart (Paper.patchVorticity scales family.patchMotion time)
        ((family.patch (finProdFinEquiv (index, patch))).boundary time label)) :
    HasDerivAt (fun parameter => Paper.patchCentroid family.patchMotion parameter index patch)
      (patchAverageVelocity scales family.patchMotion time index patch
        (biotSavart (Paper.patchVorticity scales family.patchMotion time))) time := by
  have properties := evolution.2.2.2.1 time inside
  have membership (exponent : ℝ≥0∞) := Paper.patchVorticity_memLp scales family.patchMotion time
    (fun source sourcePatch => (properties source sourcePatch).1)
    (fun source sourcePatch => (properties source sourcePatch).2.1) exponent
  have derivative := (family.patch (finProdFinEquiv (index, patch))).centroid_hasDerivAt pathInside
    (memLp_one_iff_integrable.mp (membership 1)) (membership (ENNReal.ofReal (4 : ℝ))) material
  have identity : (fun parameter => Paper.patchCentroid family.patchMotion parameter index patch) =
      (family.patch (finProdFinEquiv (index, patch))).centroid :=
    funext fun parameter => family.patchCentroid_eq parameter index patch
  rw [identity]
  have area : volume.real ((family.patch (finProdFinEquiv (index, patch))).domain time) =
      Real.pi * scales.radius (index.val + 1) ^ 2 := by
    change (volume (family.patchMotion.domain time index patch)).toReal = _
    rw [(properties index patch).2.2.1, ENNReal.toReal_ofReal (by positivity)]
  rw [area] at derivative
  exact derivative

theorem patchCentroid_hasDerivAt_point_field (family : FiniteMovingPatchFamily (count * 4))
    {scales : Scales} {horizon time : ℝ} (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (inside : time ∈ Icc 0 horizon) (index : Fin count) (patch : Fin 4)
    (pathInside : time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ label, (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
      biotSavart (Paper.patchVorticity scales family.patchMotion time)
        ((family.patch (finProdFinEquiv (index, patch))).boundary time label)) :
    HasDerivAt (fun parameter => Paper.patchCentroid family.patchMotion parameter index patch)
      (Section6.fourPointField (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
          (fun source => Paper.patchCentroid family.patchMotion time index source) patch +
        biotSavart (externalPatchVorticity scales family.patchMotion time index)
          (Paper.patchCentroid family.patchMotion time index patch) +
        quadrupoleInternalPatchResidual scales family.patchMotion time index patch +
        quadrupoleExternalReceiverResidual scales family.patchMotion time index patch) time := by
  have derivative := family.patchCentroid_hasDerivAt evolution inside index patch pathInside material
  rw [evolution.patch_average_velocity_decomposition inside index patch] at derivative
  exact derivative

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
