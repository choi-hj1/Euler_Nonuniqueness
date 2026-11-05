import EulerNonuniqueness.Section5.CascadeActualQuadrupoleComparison
import EulerNonuniqueness.Section5.CascadeActualSourceGeometry
import EulerNonuniqueness.Section6.MovingPatchFamilyCenteredRelativeSeries

noncomputable section

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_own_virtual_series :
    ∃ sourceRadius > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ {threshold referenceConstant factor : ℝ}, threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
      0 < factor → factor ≤ 1 →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ phase dipoleAngle : ℕ → ℝ, ∀ {rawCap scaleRoot shapeRadius monitor boundaryConstant : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ {time : ℝ} (inside : time ∈ Icc 0 path.stop),
      ∀ shapes : ∀ label,
        ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
        ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label),
      ∀ receiver : Fin count × Fin 4,
      ∀ receiverRadius : ℝ, ∀ receiverNonnegative : 0 ≤ receiverRadius,
      receiverRadius ≤ factor / 39321600 * ({scales with frequency := frequency} : Scales).length (receiver.1.val + 1) →
      let original := (prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes).quadrupole receiver.1
      let comparison : MovingPatchFamilySourceComparison 4 :=
        {original with receiverRadius := receiverRadius, receiverRadius_nonnegative := receiverNonnegative}
      let distance := factor / 800 * ({scales with frequency := frequency} : Scales).length (receiver.1.val + 1)
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient (Finset.univ.erase receiver.2) comparison.firstReceiver receiverRadius (power + 1) time -
          comparison.second.exteriorTaylorCoefficient (Finset.univ.erase receiver.2) comparison.secondReceiver receiverRadius (power + 1) time‖) ∧
      (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient (Finset.univ.erase receiver.2) comparison.firstReceiver receiverRadius (power + 1) time -
          comparison.second.exteriorTaylorCoefficient (Finset.univ.erase receiver.2) comparison.secondReceiver receiverRadius (power + 1) time‖) ≤
        2 * ∑ patch ∈ Finset.univ.erase receiver.2,
          ((comparison.source patch).centerDifferenceEnvelope distance 96 +
            (comparison.source patch).centeredShapeDifferenceEnvelope constant 96) := by
  obtain ⟨sourceRadius, sourcePositive, parameterRadius, parameterPositive, constant, nonnegative, bound⟩ :=
    MovingPatchFamilySourceComparison.exteriorTaylorCoefficient_exists_centered_weighted_relative_series
  refine ⟨sourceRadius, sourcePositive, constant, nonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive threshold referenceConstant factor thresholdSmall
    referenceNonnegative factorPositive factorSmall
  filter_upwards [scales.eventually_actual_cascade_source_comparison_geometry amplitudePositive ratioBound alphaPositive
    thresholdSmall referenceNonnegative factorPositive factorSmall (weight := 1) (by norm_num) parameterPositive]
    with frequency geometry
  intro count orbit sectionTime phase dipoleAngle rawCap scaleRoot shapeRadius monitor boundaryConstant
    prepared path time inside shapes receiver receiverRadius receiverNonnegative receiverSmall
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let original := (prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes).quadrupole receiver.1
  let comparison : MovingPatchFamilySourceComparison 4 :=
    {original with receiverRadius := receiverRadius, receiverRadius_nonnegative := receiverNonnegative}
  let distance := factor / 800 * changed.length (receiver.1.val + 1)
  have distancePositive : 0 < distance :=
    mul_pos (div_pos factorPositive (by norm_num)) (changed.length_pos (receiver.1.val + 1))
  have firstRatio : 2 * 96 * receiverRadius / distance ≤ 1 / 2 := by
    apply (div_le_iff₀ distancePositive).mpr
    dsimp only [distance]
    nlinarith [mul_pos factorPositive (changed.length_pos (receiver.1.val + 1))]
  have shapeRatio : 96 * 96 * receiverRadius / distance ≤ 1 / 2 := by
    apply (div_le_iff₀ distancePositive).mpr
    dsimp only [distance]
    nlinarith [mul_pos factorPositive (changed.length_pos (receiver.1.val + 1))]
  have patchGeometry (patch : Fin 4) (member : patch ∈ Finset.univ.erase receiver.2) := by
    have different : receiver ≠ (receiver.1, patch) := by
      intro same
      exact (Finset.mem_erase.mp member).1 (Prod.mk.inj same).2.symm
    have actual := geometry count orbit sectionTime phase dipoleAngle prepared.toCascadeMaterialPreparedPair
      path time inside receiver (receiver.1, patch) different
    dsimp only at actual
    have distanceIdentity : (factor / 8) * changed.individualInteractionDistance
        (receiver.1.val + 1) (receiver.1.val + 1) = distance := by
      unfold Scales.individualInteractionDistance
      simp only [ite_true]
      dsimp only [distance]
      ring
    rw [distanceIdentity] at actual
    have firstSeparated : 2 * (comparison.first.patch patch).radius + distance ≤
        ‖comparison.firstReceiver time - (comparison.first.patch patch).center time‖ := actual.2.1
    have secondSeparated : 2 * (comparison.first.patch patch).radius + distance ≤
        ‖comparison.secondReceiver time - (comparison.second.patch patch).center time‖ := actual.2.2.1
    have lower : distance ≤ ‖comparison.secondReceiver time - (comparison.second.patch patch).center time‖ := by
      linarith [(comparison.first.patch patch).radius_positive.le]
    have secondRatio : 96 * 96 * receiverRadius /
        ‖comparison.secondReceiver time - (comparison.second.patch patch).center time‖ ≤ 1 / 2 := by
      have divide := div_le_div_of_nonneg_left (show 0 ≤ 96 * 96 * receiverRadius by positivity)
        distancePositive lower
      exact divide.trans shapeRatio
    exact And.intro firstSeparated (And.intro secondSeparated (And.intro actual.2.2.2.2.2 secondRatio))
  have actual := bound 4 comparison (Finset.univ.erase receiver.2)
    (fun patch _ => mem_ball_zero_iff.mpr (shapes (finProdFinEquiv (receiver.1, patch))).1.small)
    (fun patch _ => mem_ball_zero_iff.mpr (shapes (finProdFinEquiv (receiver.1, patch))).2.small)
    (fun patch _ => (shapes (finProdFinEquiv (receiver.1, patch))).1.centroid)
    (fun patch _ => (shapes (finProdFinEquiv (receiver.1, patch))).2.centroid)
    (fun _ => distance) (fun _ _ => distancePositive)
    (fun patch member => (patchGeometry patch member).1)
    (fun patch member => (patchGeometry patch member).2.1)
    (fun patch member => (patchGeometry patch member).2.2.1) 96 (by norm_num)
    (fun _ _ => firstRatio.trans_lt (by norm_num))
    (fun patch member => (patchGeometry patch member).2.2.2.trans_lt (by norm_num))
  refine ⟨actual.1, actual.2.trans ?_⟩
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro patch member
  have firstInverse : (1 - 2 * 96 * comparison.receiverRadius / distance)⁻¹ ≤ 2 := by
    have inverse := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2)
      (show 1 / 2 ≤ 1 - 2 * 96 * comparison.receiverRadius / distance by linarith)
    norm_num only [one_div, inv_inv] at inverse
    simpa only [show (2 : ℝ) * 96 = 192 by norm_num] using inverse
  have secondInverse : (1 - 96 * 96 * comparison.receiverRadius /
      ‖comparison.secondReceiver time - (comparison.second.patch patch).center time‖)⁻¹ ≤ 2 := by
    have inverse := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2)
      (show 1 / 2 ≤ 1 - 96 * 96 * comparison.receiverRadius /
        ‖comparison.secondReceiver time - (comparison.second.patch patch).center time‖ by
        linarith [(patchGeometry patch member).2.2.2])
    norm_num only [one_div, inv_inv] at inverse
    simpa only [show (96 : ℝ) * 96 = 9216 by norm_num] using inverse
  have centerNonnegative : 0 ≤ (comparison.source patch).centerDifferenceEnvelope distance 96 := by
    unfold MovingPatchSourceComparison.centerDifferenceEnvelope
    positivity
  have shapeNonnegative : 0 ≤ (comparison.source patch).centeredShapeDifferenceEnvelope constant 96 := by
    unfold MovingPatchSourceComparison.centeredShapeDifferenceEnvelope
    exact mul_nonneg (by positivity) (comparison.source patch).spectralDifferenceBudget_nonnegative
  exact (add_le_add (mul_le_mul_of_nonneg_left firstInverse centerNonnegative)
    (mul_le_mul_of_nonneg_left secondInverse shapeNonnegative)).trans_eq (by ring)

end EulerNonuniqueness.Paper
