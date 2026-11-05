import EulerNonuniqueness.Section5.CascadeForeignReceiverAlignment
import EulerNonuniqueness.Section6.MovingSelectedStrainRegularity
import EulerNonuniqueness.Section6.MovingPatchFamilyQuadrupole
import EulerNonuniqueness.Section4.ReferencePaperShapeRegularity

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 600000

theorem FiniteMovingPatchFamily.exteriorTaylorCoefficient_continuousOn_of_local_center_gaps
    {count : ℕ} (family : FiniteMovingPatchFamily count) (selected : Finset (Fin count))
    (center : ℝ → ℂ) (radius : ℝ) (power : ℕ) (times : Set ℝ) {distance : ℝ}
    (positive : 0 < distance)
    (centerSmooth : ∀ time ∈ times, ContDiffAt ℝ 1 center time)
    (inside : ∀ time ∈ times, ∀ source ∈ selected,
      time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (gaps : ∀ time ∈ times, ∀ source ∈ selected,
      distance + 3 * (family.patch source).radius ≤ ‖center time - (family.patch source).center time‖) :
    ContinuousOn (family.exteriorTaylorCoefficient selected center radius power) times := by
  intro time member
  apply (family.exteriorTaylorCoefficient_contDiffAt_of_local_center selected center radius power
    (centerSmooth time member) (inside time member) (fun _ => distance) (fun _ _ => positive) ?_).continuousAt.continuousWithinAt
  apply (eventually_all_finset selected).mpr
  intro source sourceMember
  have strictGap : distance + 2 * (family.patch source).radius < ‖center time - (family.patch source).center time‖ := by
    linarith [(family.patch source).radius_positive, gaps time member source sourceMember]
  have continuous : ContinuousAt (fun current => ‖center current - (family.patch source).center current‖) time :=
    ((centerSmooth time member).continuousAt.sub (family.patch source).center_continuous.continuousAt).norm
  filter_upwards [continuous.eventually (Ioi_mem_nhds strictGap)] with current large
  intro position positionMember
  have bounded : ‖position - (family.patch source).center current‖ < 2 * (family.patch source).radius := by
    simpa only [Metric.mem_ball, dist_eq_norm] using
      (family.patch source).domain_subset_ball_two_radius current positionMember
  have triangle := norm_add_le (center current - position) (position - (family.patch source).center current)
  rw [sub_add_sub_cancel] at triangle
  linarith

theorem Scales.eventually_cascade_individual_source_patch_coefficient_continuous (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver : Fin count × Fin 4, ∀ source : Fin count,
      receiver.1 ≠ source → ∀ radius : ℝ, ∀ power : ℕ,
      ContinuousOn (fun time =>
        (prepared.trajectory.movingFamily.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => patchCentroid prepared.trajectory.movingFamily.patchMotion current receiver.1 receiver.2)
          radius (power + 1) time -
        (prepared.referenceWitness.trajectory.movingFamily.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current receiver.1 receiver.2)
          radius (power + 1) time) (Icc 0 path.stop) := by
  filter_upwards [scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 1000)]
    with frequency alignment radii lengths
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source different radius power
  let changed : Scales := {scales with frequency := frequency}
  let gap := |changed.location (receiver.1.val + 1) - changed.location (source.val + 1)|
  let ideal : ℂ := (changed.location (receiver.1.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
  have gapPositive : 0 < gap := changed.location_distance_pos
    (fun equality => different (Fin.ext (Nat.add_right_cancel equality)))
  have idealNorm : ‖ideal‖ = gap := by
    dsimp only [ideal, gap]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have radiusSmall : changed.radius (source.val + 1) ≤ changed.location (source.val + 1) / 1000 := by
    have first := (radii (source.val + 1)).le
    have second := (lengths (source.val + 1)).le
    change changed.radius (source.val + 1) ≤ 1 * changed.length (source.val + 1) at first
    change changed.length (source.val + 1) ≤ (1 / 1000 : ℝ) * changed.location (source.val + 1) at second
    linarith
  have globalInside (time : ℝ) (inside : time ∈ Icc 0 path.stop) : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have spacing := changed.location_sum_le_three_distance
    (show receiver.1.val + 1 ≠ source.val + 1 from fun equality => different (Fin.ext (Nat.add_right_cancel equality)))
  have oneFamily (family : FiniteMovingPatchFamily (count * 4))
      (inside : ∀ time ∈ Icc 0 path.stop, ∀ label, time ∈ Ioo (family.patch label).initialTime (family.patch label).finalTime)
      (radiusIdentity : ∀ patch, (family.patch (finProdFinEquiv (source, patch))).radius = changed.radius (source.val + 1))
      (centerIdentity : ∀ time ∈ Icc 0 path.stop, ∀ patch,
        (family.patch (finProdFinEquiv (source, patch))).center time = patchCentroid family.patchMotion time source patch)
      (aligned : ∀ time ∈ Icc 0 path.stop,
        ‖(patchCentroid family.patchMotion time receiver.1 receiver.2 - quadrupoleCenter family.patchMotion time source) - ideal‖ ≤ 3 * gap / 16)
      (extent : ∀ time ∈ Icc 0 path.stop, ∀ patch,
        ‖patchCentroid family.patchMotion time source patch - quadrupoleCenter family.patchMotion time source‖ ≤ changed.location (source.val + 1) / 100) :
      ContinuousOn ((family.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
        (fun time => patchCentroid family.patchMotion time receiver.1 receiver.2) radius (power + 1)) (Icc 0 path.stop) := by
    apply (family.quadrupoleSubfamily source).exteriorTaylorCoefficient_continuousOn_of_local_center_gaps
      Finset.univ _ radius (power + 1) _ (div_pos gapPositive (by norm_num : (0 : ℝ) < 8))
      (fun time member => family.patchCentroid_contDiffAt receiver.1 receiver.2 (inside time member _))
      (fun time member patch _ => inside time member (finProdFinEquiv (source, patch)))
    intro time member patch _
    change gap / 8 + 3 * (family.patch (finProdFinEquiv (source, patch))).radius ≤
      ‖patchCentroid family.patchMotion time receiver.1 receiver.2 -
        (family.patch (finProdFinEquiv (source, patch))).center time‖
    rw [radiusIdentity, centerIdentity time member]
    have first := norm_sub_norm_le ideal
      (patchCentroid family.patchMotion time receiver.1 receiver.2 - quadrupoleCenter family.patchMotion time source)
    rw [idealNorm, norm_sub_rev ideal] at first
    have second := norm_sub_norm_le
      (patchCentroid family.patchMotion time receiver.1 receiver.2 - quadrupoleCenter family.patchMotion time source)
      (patchCentroid family.patchMotion time source patch - quadrupoleCenter family.patchMotion time source)
    rw [sub_sub_sub_cancel_right] at second
    linarith [aligned time member, extent time member patch, changed.location_pos (receiver.1.val + 1)]
  have first := oneFamily prepared.trajectory.movingFamily (fun time member _ => globalInside time member)
    (prepared.radiusIdentity source)
    (fun time member patch => prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) (globalInside time member) source patch)
    (fun time member => (alignment count phase dipoleAngle prepared path time member receiver source different).2.1)
    (fun time member => (alignment count phase dipoleAngle prepared path time member receiver source different).2.2.2)
  have second := oneFamily prepared.referenceWitness.trajectory.movingFamily (fun time member _ => globalInside time member)
    (prepared.referenceWitness.radiusIdentity source)
    (fun time member patch => prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) (globalInside time member) source patch)
    (fun time member => (alignment count phase dipoleAngle prepared path time member receiver source different).1)
    (fun time member => (alignment count phase dipoleAngle prepared path time member receiver source different).2.2.1)
  exact first.sub second

end EulerNonuniqueness.Paper
