import EulerNonuniqueness.Section5.CascadeRelativeCenterHistory
import EulerNonuniqueness.Section6.MovingMaterialCentroidDynamics
import EulerNonuniqueness.Section6.FourPointTranslationControl

noncomputable section

open Set
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

namespace MovingCentroidGaugeTrajectory

variable {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
  {initial : MovingContourState (count * 4)}

theorem quadrupoleCenterVelocity_eq_point_field_and_forcing
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial)
    (initialCircles : ∀ label, initial.2.2 label = standardCircleBanach)
    {scales : Scales} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales trajectory.movingFamily.patchMotion horizon)
    (inside : time ∈ Icc 0 horizon) (globalInside : time ∈ Ioo (-backwardHorizon) forwardHorizon)
    (material : ∀ patch : Fin count × Fin 4, ∀ label : ℝ,
      (trajectory.movingFamily.patch (finProdFinEquiv (patch.1, patch.2))).boundaryVelocity time label =
        biotSavart (patchVorticity scales trajectory.movingFamily.patchMotion time)
          ((trajectory.movingFamily.patch (finProdFinEquiv (patch.1, patch.2))).boundary time label))
    (index : Fin count) :
    trajectory.quadrupoleCenterVelocity index time =
      fourPointArithmeticCenter (fourPointField
        (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
        (fun patch => patchCentroid trajectory.movingFamily.patchMotion time index patch)) +
      (∑ patch : Fin 4,
        (biotSavart (externalPatchVorticity scales trajectory.movingFamily.patchMotion time index)
          (patchCentroid trajectory.movingFamily.patchMotion time index patch) +
        quadrupoleInternalPatchResidual scales trajectory.movingFamily.patchMotion time index patch +
        quadrupoleExternalReceiverResidual scales trajectory.movingFamily.patchMotion time index patch)) / 4 := by
  have point (patch : Fin 4) := trajectory.movingFamily.patchCentroid_hasDerivAt_point_field
    evolution inside index patch globalInside (material (index, patch))
  have actual := (HasDerivAt.sum (u := Finset.univ) fun patch _ => point patch).div_const 4
  have mechanical := trajectory.quadrupoleCenter_hasDerivAt_quadrupoleCenterVelocity initialCircles index globalInside
  have identity := mechanical.unique actual
  apply identity.trans
  simp only [fourPointArithmeticCenter, Finset.sum_add_distrib, add_div]
  ring

end MovingCentroidGaugeTrajectory

theorem CascadeInternallyStoppedPath.paired_center_velocity_eq_point_field_and_forcing
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count}
    (path : CascadeInternallyStoppedPath prepared) {time : ℝ} (inside : time ∈ Icc 0 path.stop)
    (side : Fin 2) (index : Fin count) :
    prepared.pairedCenterVelocity side index time =
      fourPointArithmeticCenter (fourPointField
        (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
        (fun patch => patchCentroid (cascadePairedMotion prepared side) time index patch)) +
      (∑ patch : Fin 4,
        (biotSavart (externalPatchVorticity scales (cascadePairedMotion prepared side) time index)
          (patchCentroid (cascadePairedMotion prepared side) time index patch) +
        quadrupoleInternalPatchResidual scales (cascadePairedMotion prepared side) time index patch +
        quadrupoleExternalReceiverResidual scales (cascadePairedMotion prepared side) time index patch)) / 4 := by
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  fin_cases side
  · exact prepared.trajectory.quadrupoleCenterVelocity_eq_point_field_and_forcing (fun _ => rfl)
      path.evolution inside globalInside (fun patch label => path.material_boundary inside (finProdFinEquiv patch) label) index
  · simp only [cascadePairedMotion, CascadeMaterialPreparedPair.pairedCenterVelocity, Fin.cases_succ,
      prepared.referenceIdentity]
    apply prepared.referenceWitness.trajectory.quadrupoleCenterVelocity_eq_point_field_and_forcing (fun _ => rfl)
      (prepared.referenceWitness.evolution.mono (show path.stop ≤ 2 by linarith [path.stopBound])) inside globalInside
      (index := index)
    intro patch label
    rw [prepared.referenceWitness.trajectory.movingFamily.patchVorticity_eq scales prepared.referenceWitness.densityIdentity]
    exact prepared.referenceWitness.trajectory.movingFamily_material_equation_of_margin prepared.referenceWitness.marginPositive
      globalInside (prepared.referenceWitness.safe time ⟨inside.1, by linarith [inside.2, path.stopBound]⟩)
      (finProdFinEquiv patch) label

theorem CascadeInternallyStoppedPath.paired_center_velocity_difference_norm_le
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count}
    (path : CascadeInternallyStoppedPath prepared) {time : ℝ} (inside : time ∈ Icc 0 path.stop)
    (index : Fin count) :
    ‖prepared.pairedCenterVelocity 0 index time - prepared.pairedCenterVelocity 1 index time‖ ≤
      ‖fourPointArithmeticCenter (fourPointField
          (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
          (fun patch => patchCentroid (cascadePairedMotion prepared 0) time index patch)) -
        fourPointArithmeticCenter (fourPointField
          (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
          (fun patch => patchCentroid (cascadePairedMotion prepared 1) time index patch))‖ +
      (1 / 4 : ℝ) * ∑ patch : Fin 4,
        (‖biotSavart (externalPatchVorticity scales (cascadePairedMotion prepared 0) time index)
            (patchCentroid (cascadePairedMotion prepared 0) time index patch) -
          biotSavart (externalPatchVorticity scales (cascadePairedMotion prepared 1) time index)
            (patchCentroid (cascadePairedMotion prepared 1) time index patch)‖ +
        ‖(quadrupoleInternalPatchResidual scales (cascadePairedMotion prepared 0) time index patch +
            quadrupoleExternalReceiverResidual scales (cascadePairedMotion prepared 0) time index patch) -
          (quadrupoleInternalPatchResidual scales (cascadePairedMotion prepared 1) time index patch +
            quadrupoleExternalReceiverResidual scales (cascadePairedMotion prepared 1) time index patch)‖) := by
  let point := fun side : Fin 2 => fourPointArithmeticCenter (fourPointField
    (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
    (fun patch => patchCentroid (cascadePairedMotion prepared side) time index patch))
  let exterior := fun (side : Fin 2) (patch : Fin 4) =>
    biotSavart (externalPatchVorticity scales (cascadePairedMotion prepared side) time index)
      (patchCentroid (cascadePairedMotion prepared side) time index patch)
  let residual := fun (side : Fin 2) (patch : Fin 4) =>
    quadrupoleInternalPatchResidual scales (cascadePairedMotion prepared side) time index patch +
      quadrupoleExternalReceiverResidual scales (cascadePairedMotion prepared side) time index patch
  have first := path.paired_center_velocity_eq_point_field_and_forcing inside 0 index
  have second := path.paired_center_velocity_eq_point_field_and_forcing inside 1 index
  change prepared.pairedCenterVelocity 0 index time =
    point 0 + (∑ patch, (exterior 0 patch + _ + _)) / 4 at first
  have firstIdentity : prepared.pairedCenterVelocity 0 index time =
      point 0 + (∑ patch, (exterior 0 patch + residual 0 patch)) / 4 := by
    simpa only [residual, add_assoc] using first
  have secondIdentity : prepared.pairedCenterVelocity 1 index time =
      point 1 + (∑ patch, (exterior 1 patch + residual 1 patch)) / 4 := by
    simpa only [point, exterior, residual, add_assoc] using second
  change ‖prepared.pairedCenterVelocity 0 index time - prepared.pairedCenterVelocity 1 index time‖ ≤
    ‖point 0 - point 1‖ + (1 / 4 : ℝ) *
      ∑ patch, (‖exterior 0 patch - exterior 1 patch‖ + ‖residual 0 patch - residual 1 patch‖)
  rw [firstIdentity, secondIdentity]
  have identity : point 0 + (∑ patch, (exterior 0 patch + residual 0 patch)) / 4 -
      (point 1 + (∑ patch, (exterior 1 patch + residual 1 patch)) / 4) =
      (point 0 - point 1) +
        (∑ patch, ((exterior 0 patch - exterior 1 patch) + (residual 0 patch - residual 1 patch))) / 4 := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [identity]
  apply (norm_add_le _ _).trans
  apply add_le_add_left
  rw [norm_div, Complex.norm_ofNat]
  have total := (norm_sum_le (Finset.univ : Finset (Fin 4))
    (fun patch => (exterior 0 patch - exterior 1 patch) + (residual 0 patch - residual 1 patch))).trans
    (Finset.sum_le_sum fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) => norm_add_le _ _)
  have divided := div_le_div_of_nonneg_right total (by norm_num : (0 : ℝ) ≤ 4)
  exact divided.trans_eq (by ring)

end EulerNonuniqueness.Paper
