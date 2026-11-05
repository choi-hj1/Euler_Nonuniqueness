import EulerNonuniqueness.Section6.FourPointCenterProjection
import EulerNonuniqueness.Section6.MovingMaterialCentroidDynamics
import EulerNonuniqueness.Section6.MovingBlockRelativeCentroid

noncomputable section

open Set
open scoped BigOperators NNReal

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

def quadrupoleCenteredForcing {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) : FourPointConfiguration :=
  fourPointCenterProjection (fun patch =>
    biotSavart (externalPatchVorticity scales motion time index) (patchCentroid motion time index patch) +
      quadrupoleInternalPatchResidual scales motion time index patch +
      quadrupoleExternalReceiverResidual scales motion time index patch)

theorem FiniteMovingPatchFamily.centeredCentroid_hasDerivAt_point_field {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) {scales : Scales} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (inside : time ∈ Icc 0 horizon) (index : Fin count)
    (pathInside : ∀ patch, time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ patch label, (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
      biotSavart (Paper.patchVorticity scales family.patchMotion time)
        ((family.patch (finProdFinEquiv (index, patch))).boundary time label)) :
    HasDerivAt (fun current => fourPointCenterProjection (fun patch => patchCentroid family.patchMotion current index patch))
      (fourPointCenteredField (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
          (fourPointCenterProjection (fun patch => patchCentroid family.patchMotion time index patch)) +
        quadrupoleCenteredForcing scales family.patchMotion time index) time := by
  apply fourPointCenterProjection_forced_equation
  apply hasDerivAt_pi.mpr
  intro patch
  have actual := family.patchCentroid_hasDerivAt_point_field evolution inside index patch
    (pathInside patch) (material patch)
  convert actual using 1 <;> simp only [Pi.add_apply] <;> ring

end EulerNonuniqueness.Paper
