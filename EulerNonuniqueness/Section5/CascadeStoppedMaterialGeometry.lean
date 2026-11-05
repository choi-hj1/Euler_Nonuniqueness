import EulerNonuniqueness.Section5.CascadeInternallyStoppedPath
import EulerNonuniqueness.Section5.CascadeMaterialCommonPhase
import EulerNonuniqueness.Section5.CascadeMaterialCenterGeometry
import EulerNonuniqueness.Section3.MovingCentroidGaugeDisjointness

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.CascadeInternallyStoppedPath

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
  {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
    scaleRoot shapeRadius factor monitor boundaryConstant count}

theorem material_boundary (path : CascadeInternallyStoppedPath prepared)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (label : Fin (count * 4)) (angle : ℝ) :
    (prepared.trajectory.movingFamily.patch label).boundaryVelocity time angle =
      biotSavart (patchVorticity scales prepared.trajectory.movingFamily.patchMotion time)
        ((prepared.trajectory.movingFamily.patch label).boundary time angle) := by
  rw [prepared.trajectory.movingFamily.patchVorticity_eq scales prepared.densityIdentity]
  exact prepared.trajectory.movingFamily_material_equation_of_margin prepared.marginPositive
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
    (path.safe time inside).le label angle

theorem common_phase (path : CascadeInternallyStoppedPath prepared)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (index : Fin count) (patch : Fin 4) :
    (prepared.referenceWitness.trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).phase time =
      (prepared.trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).phase time ∧
    (prepared.trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).phase time =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4 * time / 2 :=
  prepared.common_material_phase path.stopBound inside (fun time member => (path.safe time member).le) index patch

theorem internal_centroid_gap (path : CascadeInternallyStoppedPath prepared)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (index : Fin count) (first second : Fin 4)
    (different : first ≠ second) :
    factor * scales.length (index.val + 1) ≤
      ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time index first -
        patchCentroid prepared.trajectory.movingFamily.patchMotion time index second‖ := by
  have estimate := path.internalClosed time inside (index, first) (index, second)
  rw [cascadeInternalGapMonitor, if_pos (show (index, first).1 = (index, second).1 ∧
    (index, first).2 ≠ (index, second).2 from ⟨rfl, different⟩)] at estimate
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 := ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  rw [prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside,
    prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside] at estimate
  exact sub_nonpos.mp estimate

theorem centroid_extent (path : CascadeInternallyStoppedPath prepared)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (index : Fin count) (patch : Fin 4) :
    ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time index patch -
      quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index‖ <
        scales.location (index.val + 1) / 100 := by
  have estimate := path.externalMonitors time inside (.extent (index, patch))
  change ‖prepared.trajectory.movingFamily.cascadeCenters time (index, patch) -
    cascadeBlockCenter (prepared.trajectory.movingFamily.cascadeCenters time) index‖ - _ < 0 at estimate
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 := ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  rw [prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside,
    prepared.trajectory.cascadeBlockCenter_eq_quadrupoleCenter (fun _ => rfl) globalInside] at estimate
  exact sub_neg.mp estimate

theorem quadrupole_pair_bounds (path : CascadeInternallyStoppedPath prepared)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (first second : Fin count) (different : first ≠ second) :
    |scales.location (first.val + 1) - scales.location (second.val + 1)| / 2 <
      ‖quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time first -
        quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time second‖ ∧
    ‖quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time first -
        quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time second‖ <
      2 * |scales.location (first.val + 1) - scales.location (second.val + 1)| := by
  have lower := path.externalMonitors time inside (.lower first second)
  have upper := path.externalMonitors time inside (.upper first second)
  change cascadeAnchorLowerMonitor scales first second _ < 0 at lower
  change cascadeAnchorUpperMonitor scales first second _ < 0 at upper
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 := ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  rw [cascadeAnchorLowerMonitor, if_neg different,
    prepared.trajectory.cascadeBlockCenter_eq_quadrupoleCenter (fun _ => rfl) globalInside,
    prepared.trajectory.cascadeBlockCenter_eq_quadrupoleCenter (fun _ => rfl) globalInside] at lower
  rw [cascadeAnchorUpperMonitor, if_neg different,
    prepared.trajectory.cascadeBlockCenter_eq_quadrupoleCenter (fun _ => rfl) globalInside,
    prepared.trajectory.cascadeBlockCenter_eq_quadrupoleCenter (fun _ => rfl) globalInside] at upper
  exact ⟨sub_neg.mp lower, sub_neg.mp upper⟩

theorem patches_disjoint (path : CascadeInternallyStoppedPath prepared) :
    PatchesDisjoint prepared.trajectory.movingFamily.patchMotion path.stop :=
  prepared.trajectory.patchesDisjoint_on_interval (by linarith [path.stopBound])

theorem premature_contact (path : CascadeInternallyStoppedPath prepared) (premature : path.stop < 1) :
    ∃ index : Fin count, ∃ first second : Fin 4, first ≠ second ∧
      ‖patchCentroid prepared.trajectory.movingFamily.patchMotion path.stop index first -
        patchCentroid prepared.trajectory.movingFamily.patchMotion path.stop index second‖ =
          factor * scales.length (index.val + 1) := by
  rcases path.terminalContact with complete | ⟨⟨index, first⟩, ⟨other, second⟩, zero⟩
  · linarith
  unfold cascadeInternalGapMonitor at zero
  split_ifs at zero with condition
  · rcases condition with ⟨same, different⟩
    change index = other at same
    subst other
    have globalInside : path.stop ∈ Ioo (-(1 : ℝ)) 3 := ⟨by linarith [path.stopPositive], by linarith [path.stopBound]⟩
    rw [prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside,
      prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside] at zero
    exact ⟨index, first, second, different, by linarith⟩
  · norm_num at zero

end EulerNonuniqueness.Paper.CascadeInternallyStoppedPath
