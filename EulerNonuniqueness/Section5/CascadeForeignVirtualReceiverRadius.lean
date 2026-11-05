import EulerNonuniqueness.Section5.CascadeActualSourceGeometry
import EulerNonuniqueness.Section3.ExteriorCoefficientWeights
import EulerNonuniqueness.Section6.MovingForeignQuadrupole
import EulerNonuniqueness.Section6.MovingExteriorCoefficientBound

noncomputable section

open Set Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem Scales.eventually_cascade_foreign_virtual_receiver_radius (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {threshold referenceConstant factor : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ phase dipoleAngle : ℕ → ℝ, ∀ {scaleRoot shapeRadius monitor boundaryConstant : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ time ∈ Icc 0 path.stop,
      ∀ receiver : Fin count × Fin 4,
      let changed : Scales := {scales with frequency := frequency}
      let virtualRadius := factor / 39321600 * changed.location (receiver.1.val + 1)
      let distance := factor / 1600 * changed.location (receiver.1.val + 1)
      let first := prepared.referenceWitness.trajectory.movingFamily
      let second := prepared.trajectory.movingFamily
      let selected := foreignQuadrupolePatchLabels receiver.1
      0 < virtualRadius ∧ 0 < distance ∧
      (first.patch (finProdFinEquiv receiver)).radius ≤ virtualRadius ∧
      24 * virtualRadius / distance < 1 ∧
      (∀ source ∈ selected, ∀ position ∈ (first.patch source).domain time,
        distance ≤ ‖(first.patch (finProdFinEquiv receiver)).center time - position‖) ∧
      (∀ source ∈ selected, ∀ position ∈ (second.patch source).domain time,
        distance ≤ ‖(second.patch (finProdFinEquiv receiver)).center time - position‖) ∧
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
        ‖first.exteriorTaylorCoefficient selected (first.patch (finProdFinEquiv receiver)).center
          virtualRadius (power + 1) time‖) ∧
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
        ‖second.exteriorTaylorCoefficient selected (second.patch (finProdFinEquiv receiver)).center
          virtualRadius (power + 1) time‖) := by
  filter_upwards [scales.eventually_actual_cascade_source_comparison_geometry
      amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative factorPositive factorSmall
      (weight := 1) (by norm_num) (parameterRadius := 1) (by norm_num),
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio)
      (show 0 < factor / 39321600 by positivity),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1)]
    with frequency geometry radii lengths
  intro count orbit sectionTime phase dipoleAngle scaleRoot shapeRadius monitor boundaryConstant
    prepared path time inside receiver
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.referenceWitness.trajectory.movingFamily
  let second := prepared.trajectory.movingFamily
  let selected := foreignQuadrupolePatchLabels receiver.1
  let distance := factor / 1600 * changed.location (receiver.1.val + 1)
  let virtualRadius := factor / 39321600 * changed.location (receiver.1.val + 1)
  have locationPositive := changed.location_pos (receiver.1.val + 1)
  have distancePositive : 0 < distance := by dsimp only [distance]; positivity
  have virtualPositive : 0 < virtualRadius := by dsimp only [virtualRadius]; positivity
  have physicalSmall : (first.patch (finProdFinEquiv receiver)).radius ≤ virtualRadius := by
    have receiverRadius : (first.patch (finProdFinEquiv receiver)).radius = changed.radius (receiver.1.val + 1) :=
      prepared.referenceWitness.radiusIdentity receiver.1 receiver.2
    rw [receiverRadius]
    apply (radii (receiver.1.val + 1)).le.trans
    change factor / 39321600 * changed.length (receiver.1.val + 1) ≤ _
    exact mul_le_mul_of_nonneg_left (by simpa only [one_mul] using (lengths (receiver.1.val + 1)).le)
      (by positivity)
  have sourceGeometry (label : Fin (count * 4)) (member : label ∈ selected) :
      2 * (first.patch label).radius + distance ≤
        ‖(first.patch (finProdFinEquiv receiver)).center time - (first.patch label).center time‖ ∧
      2 * (second.patch label).radius + distance ≤
        ‖(second.patch (finProdFinEquiv receiver)).center time - (second.patch label).center time‖ := by
    let source := finProdFinEquiv.symm label
    have sourceIdentity : finProdFinEquiv source = label := finProdFinEquiv.apply_symm_apply label
    have sourceDifferent : source.1 ≠ receiver.1 := by
      apply (mem_foreignQuadrupolePatchLabels receiver.1 source.1 source.2).mp
      simpa only [sourceIdentity] using member
    have different : receiver ≠ source := fun equality => sourceDifferent (congrArg Prod.fst equality.symm)
    have indexDifferent : receiver.1.val + 1 ≠ source.1.val + 1 :=
      fun equality => sourceDifferent (Fin.ext (Nat.add_right_cancel equality)).symm
    have interaction : changed.individualInteractionDistance (receiver.1.val + 1) (source.1.val + 1) =
        |changed.location (receiver.1.val + 1) - changed.location (source.1.val + 1)| / 8 := by
      simp only [Scales.individualInteractionDistance, if_neg indexDifferent.symm]
    have locations := changed.location_sum_le_three_distance indexDifferent
    have gapBound : distance ≤ factor / 8 *
        changed.individualInteractionDistance (receiver.1.val + 1) (source.1.val + 1) := by
      rw [interaction]
      have receiverBound : changed.location (receiver.1.val + 1) ≤
          3 * |changed.location (receiver.1.val + 1) - changed.location (source.1.val + 1)| := by
        linarith [changed.location_pos (source.1.val + 1)]
      dsimp only [distance]
      nlinarith [mul_le_mul_of_nonneg_left receiverBound factorPositive.le]
    have actual := geometry count orbit sectionTime phase dipoleAngle prepared path time inside receiver source different
    have sourceRadiusEqual : (first.patch label).radius = (second.patch label).radius := by
      rw [← sourceIdentity]
      change prepared.referenceWitness.configuration.radius (finProdFinEquiv source) =
        prepared.configuration.radius (finProdFinEquiv source)
      rw [prepared.referenceWitness.radiusIdentity source.1 source.2, prepared.radiusIdentity source.1 source.2]
    have firstGap := actual.2.1
    have secondGap := actual.2.2.1
    rw [sourceIdentity] at firstGap secondGap
    change 2 * (first.patch label).radius + _ ≤ _ at firstGap secondGap
    rw [sourceRadiusEqual] at secondGap
    exact ⟨by linarith, by linarith⟩
  have firstSeparated (source : Fin (count * 4)) (member : source ∈ selected)
      (position : ℂ) (inDomain : position ∈ (first.patch source).domain time) :
      distance ≤ ‖(first.patch (finProdFinEquiv receiver)).center time - position‖ := by
    have sourceBound := (Metric.mem_ball.mp ((first.patch source).domain_subset_ball time inDomain)).le
    rw [dist_eq_norm] at sourceBound
    have triangle := norm_add_le ((first.patch (finProdFinEquiv receiver)).center time - position)
      (position - (first.patch source).center time)
    rw [sub_add_sub_cancel] at triangle
    linarith [(sourceGeometry source member).1]
  have secondSeparated (source : Fin (count * 4)) (member : source ∈ selected)
      (position : ℂ) (inDomain : position ∈ (second.patch source).domain time) :
      distance ≤ ‖(second.patch (finProdFinEquiv receiver)).center time - position‖ := by
    have sourceBound := (Metric.mem_ball.mp ((second.patch source).domain_subset_ball time inDomain)).le
    rw [dist_eq_norm] at sourceBound
    have triangle := norm_add_le ((second.patch (finProdFinEquiv receiver)).center time - position)
      (position - (second.patch source).center time)
    rw [sub_add_sub_cancel] at triangle
    linarith [(sourceGeometry source member).2]
  have ratioSmall : 96 * virtualRadius / distance < 1 := by
    apply (div_lt_one distancePositive).mpr
    dsimp only [virtualRadius, distance]
    nlinarith [mul_pos factorPositive locationPositive]
  have small24 : 24 * virtualRadius / distance < 1 :=
    (div_le_div_of_nonneg_right (by nlinarith [virtualPositive]) distancePositive.le).trans_lt ratioSmall
  refine ⟨virtualPositive, distancePositive, physicalSmall, small24, firstSeparated, secondSeparated, ?_, ?_⟩
  · change Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖first.exteriorTaylorCoefficient selected (first.patch (finProdFinEquiv receiver)).center
        virtualRadius (power + 1) time‖)
    simp_rw [first.exteriorTaylorCoefficient_eq_vorticityCoefficient selected
      (first.patch (finProdFinEquiv receiver)).center virtualRadius time _ distancePositive firstSeparated]
    exact Section6.summable_exteriorVorticityCoefficient_weight (first.subfamilyVorticity_integrable selected time)
      _ virtualPositive.le distancePositive (by norm_num)
      (first.subfamily_support_separated selected _ time distance firstSeparated) ratioSmall
  · change Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖second.exteriorTaylorCoefficient selected (second.patch (finProdFinEquiv receiver)).center
        virtualRadius (power + 1) time‖)
    simp_rw [second.exteriorTaylorCoefficient_eq_vorticityCoefficient selected
      (second.patch (finProdFinEquiv receiver)).center virtualRadius time _ distancePositive secondSeparated]
    exact Section6.summable_exteriorVorticityCoefficient_weight (second.subfamilyVorticity_integrable selected time)
      _ virtualPositive.le distancePositive (by norm_num)
      (second.subfamily_support_separated selected _ time distance secondSeparated) ratioSmall

end EulerNonuniqueness.Paper
