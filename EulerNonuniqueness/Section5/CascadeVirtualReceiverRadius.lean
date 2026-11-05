import EulerNonuniqueness.Section5.CascadeActualSourceGeometry
import EulerNonuniqueness.Section3.ExteriorCoefficientWeights
import EulerNonuniqueness.Section6.MovingExteriorCoefficientBound

noncomputable section

open Set Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

theorem Scales.eventually_cascade_virtual_receiver_radius (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {threshold referenceConstant factor : ℝ} (thresholdSmall : threshold ≤ 1 / 8)
    (referenceNonnegative : 0 ≤ referenceConstant) (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ phase dipoleAngle : ℕ → ℝ, ∀ {scaleRoot shapeRadius monitor boundaryConstant : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ time ∈ Icc 0 path.stop,
      ∀ receiver : Fin count × Fin 4,
      let changed : Scales := {scales with frequency := frequency}
      let virtualRadius := factor / 39321600 * changed.length (receiver.1.val + 1)
      let distance := factor / 1600 * changed.length (receiver.1.val + 1)
      let first := prepared.referenceWitness.trajectory.movingFamily
      let second := prepared.trajectory.movingFamily
      0 < virtualRadius ∧ 0 < distance ∧
      (first.patch (finProdFinEquiv receiver)).radius ≤ virtualRadius ∧
      (∀ source ∈ Finset.univ.erase (finProdFinEquiv receiver), ∀ position ∈ (first.patch source).domain time,
        distance ≤ ‖(first.patch (finProdFinEquiv receiver)).center time - position‖) ∧
      (∀ source ∈ Finset.univ.erase (finProdFinEquiv receiver), ∀ position ∈ (second.patch source).domain time,
        distance ≤ ‖(second.patch (finProdFinEquiv receiver)).center time - position‖) ∧
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
        ‖first.exteriorTaylorCoefficient (Finset.univ.erase (finProdFinEquiv receiver))
          (first.patch (finProdFinEquiv receiver)).center virtualRadius (power + 1) time‖) ∧
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
        ‖second.exteriorTaylorCoefficient (Finset.univ.erase (finProdFinEquiv receiver))
          (second.patch (finProdFinEquiv receiver)).center virtualRadius (power + 1) time‖) := by
  filter_upwards [scales.eventually_actual_cascade_source_comparison_geometry amplitudePositive ratioBound alphaPositive
      thresholdSmall referenceNonnegative factorPositive factorSmall (weight := 1) (by norm_num)
      (parameterRadius := 1) (by norm_num),
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio)
      (show 0 < factor / 39321600 by positivity),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1)]
    with frequency geometry radii lengths
  intro count orbit sectionTime phase dipoleAngle scaleRoot shapeRadius monitor boundaryConstant prepared path time inside receiver
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.referenceWitness.trajectory.movingFamily
  let second := prepared.trajectory.movingFamily
  let distance := factor / 1600 * changed.length (receiver.1.val + 1)
  let virtualRadius := factor / 39321600 * changed.length (receiver.1.val + 1)
  have lengthPositive := changed.length_pos (receiver.1.val + 1)
  have distancePositive : 0 < distance := by dsimp only [distance]; positivity
  have virtualPositive : 0 < virtualRadius := by dsimp only [virtualRadius]; positivity
  have receiverRadius : (first.patch (finProdFinEquiv receiver)).radius = changed.radius (receiver.1.val + 1) :=
    prepared.referenceWitness.radiusIdentity receiver.1 receiver.2
  have physicalSmall : (first.patch (finProdFinEquiv receiver)).radius ≤ virtualRadius := by
    rw [receiverRadius]
    exact (radii (receiver.1.val + 1)).le
  have interactionLower (source : Fin count) : changed.length (receiver.1.val + 1) / 100 ≤
      changed.individualInteractionDistance (receiver.1.val + 1) (source.val + 1) := by
    unfold Scales.individualInteractionDistance
    split_ifs with same
    · exact le_rfl
    · have indexDifferent : receiver.1.val + 1 ≠ source.val + 1 := Ne.symm same
      have locationBound := changed.location_sum_le_three_distance indexDifferent
      have lengthBound : changed.length (receiver.1.val + 1) ≤ changed.location (receiver.1.val + 1) := by
        simpa only [one_mul] using (lengths (receiver.1.val + 1)).le
      linarith [changed.location_pos (source.val + 1)]
  have sourceGeometry (label : Fin (count * 4)) (member : label ∈ Finset.univ.erase (finProdFinEquiv receiver)) := by
    let source := finProdFinEquiv.symm label
    have sourceIdentity : finProdFinEquiv source = label := finProdFinEquiv.apply_symm_apply label
    have different : receiver ≠ source := by
      intro equality
      exact (Finset.mem_erase.mp member).1 (by rw [← sourceIdentity, ← equality])
    have actual := geometry count orbit sectionTime phase dipoleAngle prepared path time inside receiver source different
    have gapBound : distance ≤ (factor / 8) * changed.individualInteractionDistance
        (receiver.1.val + 1) (source.1.val + 1) := by
      have lower := mul_le_mul_of_nonneg_left (interactionLower source.1) (show 0 ≤ factor / 8 by positivity)
      dsimp only [distance]
      nlinarith
    have sourceRadiusEqual : (first.patch label).radius = (second.patch label).radius := by
      rw [← sourceIdentity]
      change prepared.referenceWitness.configuration.radius (finProdFinEquiv source) =
        prepared.configuration.radius (finProdFinEquiv source)
      rw [prepared.referenceWitness.radiusIdentity source.1 source.2, prepared.radiusIdentity source.1 source.2]
    have firstGap : 2 * (first.patch label).radius + distance ≤
        ‖(first.patch (finProdFinEquiv receiver)).center time - (first.patch label).center time‖ := by
      have estimate := actual.2.1
      change 2 * (first.patch (finProdFinEquiv source)).radius +
        (factor / 8) * changed.individualInteractionDistance (receiver.1.val + 1) (source.1.val + 1) ≤ _ at estimate
      rw [sourceIdentity] at estimate
      linarith
    have secondGap : 2 * (second.patch label).radius + distance ≤
        ‖(second.patch (finProdFinEquiv receiver)).center time - (second.patch label).center time‖ := by
      have estimate := actual.2.2.1
      change 2 * (first.patch (finProdFinEquiv source)).radius +
        (factor / 8) * changed.individualInteractionDistance (receiver.1.val + 1) (source.1.val + 1) ≤ _ at estimate
      rw [sourceIdentity, sourceRadiusEqual] at estimate
      linarith
    exact And.intro firstGap secondGap
  have firstSeparated (source : Fin (count * 4)) (member : source ∈ Finset.univ.erase (finProdFinEquiv receiver))
      (position : ℂ) (inside : position ∈ (first.patch source).domain time) :
      distance ≤ ‖(first.patch (finProdFinEquiv receiver)).center time - position‖ := by
    have sourceBound := (Metric.mem_ball.mp ((first.patch source).domain_subset_ball time inside)).le
    rw [dist_eq_norm] at sourceBound
    have triangle := norm_add_le ((first.patch (finProdFinEquiv receiver)).center time - position)
      (position - (first.patch source).center time)
    rw [sub_add_sub_cancel] at triangle
    linarith [(sourceGeometry source member).1]
  have secondSeparated (source : Fin (count * 4)) (member : source ∈ Finset.univ.erase (finProdFinEquiv receiver))
      (position : ℂ) (inside : position ∈ (second.patch source).domain time) :
      distance ≤ ‖(second.patch (finProdFinEquiv receiver)).center time - position‖ := by
    have sourceBound := (Metric.mem_ball.mp ((second.patch source).domain_subset_ball time inside)).le
    rw [dist_eq_norm] at sourceBound
    have triangle := norm_add_le ((second.patch (finProdFinEquiv receiver)).center time - position)
      (position - (second.patch source).center time)
    rw [sub_add_sub_cancel] at triangle
    linarith [(sourceGeometry source member).2]
  have ratioSmall : 96 * virtualRadius / distance < 1 := by
    apply (div_lt_one distancePositive).mpr
    dsimp only [virtualRadius, distance]
    nlinarith [mul_pos factorPositive lengthPositive]
  refine ⟨virtualPositive, distancePositive, physicalSmall, firstSeparated, secondSeparated, ?_, ?_⟩
  · change Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖first.exteriorTaylorCoefficient (Finset.univ.erase (finProdFinEquiv receiver))
        (first.patch (finProdFinEquiv receiver)).center virtualRadius (power + 1) time‖)
    simp_rw [first.exteriorTaylorCoefficient_eq_vorticityCoefficient (Finset.univ.erase (finProdFinEquiv receiver))
      (first.patch (finProdFinEquiv receiver)).center virtualRadius time _ distancePositive firstSeparated]
    exact Section6.summable_exteriorVorticityCoefficient_weight
      (first.subfamilyVorticity_integrable (Finset.univ.erase (finProdFinEquiv receiver)) time) _
      virtualPositive.le distancePositive (by norm_num)
      (first.subfamily_support_separated (Finset.univ.erase (finProdFinEquiv receiver))
        ((first.patch (finProdFinEquiv receiver)).center time) time distance firstSeparated) ratioSmall
  · change Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖second.exteriorTaylorCoefficient (Finset.univ.erase (finProdFinEquiv receiver))
        (second.patch (finProdFinEquiv receiver)).center virtualRadius (power + 1) time‖)
    simp_rw [second.exteriorTaylorCoefficient_eq_vorticityCoefficient (Finset.univ.erase (finProdFinEquiv receiver))
      (second.patch (finProdFinEquiv receiver)).center virtualRadius time _ distancePositive secondSeparated]
    exact Section6.summable_exteriorVorticityCoefficient_weight
      (second.subfamilyVorticity_integrable (Finset.univ.erase (finProdFinEquiv receiver)) time) _
      virtualPositive.le distancePositive (by norm_num)
      (second.subfamily_support_separated (Finset.univ.erase (finProdFinEquiv receiver))
        ((second.patch (finProdFinEquiv receiver)).center time) time distance secondSeparated) ratioSmall

end EulerNonuniqueness.Paper
