import EulerNonuniqueness.Section6.MovingMaterialCentroidDynamics
import EulerNonuniqueness.Section6.ForcedNegativeLabelBridge

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem centroid_outgoing_equation {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    {scales : Scales} {horizon time : ℝ} (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (inside : time ∈ Icc 0 horizon) (index : Fin count)
    (pathInside : ∀ patch : Fin 4, time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ patch label, (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
      biotSavart (Paper.patchVorticity scales family.patchMotion time)
        ((family.patch (finProdFinEquiv (index, patch))).boundary time label)) :
    let trajectory := fun current patch => patchCentroid family.patchMotion current index patch
    let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
    let residual := fun patch => quadrupoleInternalPatchResidual scales family.patchMotion time index patch +
      quadrupoleExternalReceiverResidual scales family.patchMotion time index patch
    ∀ target, HasDerivAt
      (fun current => Section6.relabelNegativePoints (trajectory current) target)
      (Section6.fourPointField coefficient (Section6.relabelNegativePoints (trajectory time)) target +
        biotSavart (externalPatchVorticity scales family.patchMotion time index)
          (Section6.relabelNegativePoints (trajectory time) target) +
        Section6.relabelNegativePoints residual target) time := by
  dsimp only
  apply Section6.relabelNegativePoints_forced_equation
  intro patch
  simpa only [add_assoc] using family.patchCentroid_hasDerivAt_point_field evolution inside index patch
    (pathInside patch) (material patch)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
