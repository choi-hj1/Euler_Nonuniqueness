import EulerNonuniqueness.Section5.CascadeCenterVelocityDecomposition
import EulerNonuniqueness.Section6.PaperDilationForcingParts

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem CascadeInternallyStoppedPath.paired_center_velocity_difference_norm_le_array
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count}
    (path : CascadeInternallyStoppedPath prepared) {time : ℝ} (inside : time ∈ Icc 0 path.stop)
    (index : Fin count) :
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.reference
    ‖prepared.pairedCenterVelocity 0 index time - prepared.pairedCenterVelocity 1 index time‖ ≤
      ‖fourPointArithmeticCenter (fourPointField
          (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
          (fun patch => patchCentroid first time index patch)) -
        fourPointArithmeticCenter (fourPointField
          (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
          (fun patch => patchCentroid second time index patch))‖ +
      (1 / 4 : ℝ) * (∑ patch : Fin 4,
        ‖biotSavart (externalPatchVorticity scales first time index) (patchCentroid first time index patch) -
          biotSavart (externalPatchVorticity scales second time index) (patchCentroid second time index patch)‖) +
      ‖quadrupoleDilationPatchError scales first index time - quadrupoleDilationPatchError scales second index time‖ := by
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let error := quadrupoleDilationPatchError scales first index time - quadrupoleDilationPatchError scales second index time
  let exterior := fun patch : Fin 4 =>
    ‖biotSavart (externalPatchVorticity scales first time index) (patchCentroid first time index patch) -
      biotSavart (externalPatchVorticity scales second time index) (patchCentroid second time index patch)‖
  have actual := path.paired_center_velocity_difference_norm_le inside index
  change ‖prepared.pairedCenterVelocity 0 index time - prepared.pairedCenterVelocity 1 index time‖ ≤
    ‖fourPointArithmeticCenter (fourPointField
        (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
        (fun patch => patchCentroid first time index patch)) -
      fourPointArithmeticCenter (fourPointField
        (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
        (fun patch => patchCentroid second time index patch))‖ +
    (1 / 4 : ℝ) * ∑ patch : Fin 4, (exterior patch + ‖error patch‖) at actual
  have errorBound : (∑ patch : Fin 4, ‖error patch‖) ≤ 4 * ‖error‖ := by
    calc
      (∑ patch : Fin 4, ‖error patch‖) ≤ ∑ _patch : Fin 4, ‖error‖ :=
        Finset.sum_le_sum fun patch _ => norm_le_pi_norm error patch
      _ = 4 * ‖error‖ := by simp
  rw [Finset.sum_add_distrib] at actual
  exact (actual.trans (add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_left errorBound _)
    (by norm_num : (0 : ℝ) ≤ 1 / 4)) _)).trans_eq (by dsimp only [first, second, exterior, error]; ring)

end EulerNonuniqueness.Paper
