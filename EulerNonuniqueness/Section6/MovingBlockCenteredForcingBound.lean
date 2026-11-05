import EulerNonuniqueness.Section6.MovingBlockCenteredPointEquation
import EulerNonuniqueness.Section6.FourPointExternalCentering
import EulerNonuniqueness.Section7.PaperDipoleDynamics
import EulerNonuniqueness.Section6.NegativeLabelBridge

noncomputable section

open Set
open scoped NNReal

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem quadrupoleCenteredForcing_norm_le {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) {region : Set ℂ} {strain : ℝ≥0} {residualBound : ℝ}
    (externalLipschitz : LipschitzOnWith strain (biotSavart (externalPatchVorticity scales motion time index)) region)
    (inside : ∀ patch, patchCentroid motion time index patch ∈ region)
    (residual : ‖dipolePatchResidual scales motion time index‖ ≤ residualBound) :
    ‖quadrupoleCenteredForcing scales motion time index‖ ≤
      2 * (strain : ℝ) * ‖fourPointCenterProjection (fun patch => patchCentroid motion time index patch)‖ +
        2 * residualBound := by
  let external : FourPointConfiguration := fun patch =>
    biotSavart (externalPatchVorticity scales motion time index) (patchCentroid motion time index patch)
  let rawResidual : FourPointConfiguration := fun patch => quadrupoleInternalPatchResidual scales motion time index patch +
    quadrupoleExternalReceiverResidual scales motion time index patch
  have residualIdentity : dipolePatchResidual scales motion time index = relabelNegativePoints rawResidual := rfl
  have rawBound : ‖rawResidual‖ ≤ residualBound := by
    rw [residualIdentity, relabelNegativePoints_norm] at residual
    exact residual
  have forcingIdentity : quadrupoleCenteredForcing scales motion time index =
      fourPointCenterProjection external + fourPointCenterProjection rawResidual := by
    rw [← fourPointCenterProjection_add]
    apply congrArg fourPointCenterProjection
    funext patch
    simp only [Pi.add_apply, external, rawResidual]
    ring
  have externalBound := fourPointCenterProjection_external_norm_le externalLipschitz inside
    (fun patch => norm_le_pi_norm (fourPointCenterProjection (fun patch => patchCentroid motion time index patch)) patch)
  rw [forcingIdentity]
  exact (norm_add_le _ _).trans (add_le_add externalBound
    ((fourPointCenterProjection_norm_le rawResidual).trans (mul_le_mul_of_nonneg_left rawBound (by norm_num))))

end EulerNonuniqueness.Paper
