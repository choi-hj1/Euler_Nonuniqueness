import EulerNonuniqueness.Section5.CascadeOwnBoundarySourceReturn

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_own_local_virtual_return :
    ∃ sourceRadius > (0 : ℝ), ∃ rawCap > (0 : ℝ),
    ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 → ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ {threshold referenceConstant : ℝ}, threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ phase dipoleAngle : ℕ → ℝ, ∀ {scaleRoot shapeRadius monitor boundaryConstant : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ {time : ℝ} (inside : time ∈ Icc 0 path.stop), ∀ receiver : Fin count × Fin 4,
    ∃ shapes : ∀ label,
      ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
      ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label),
    ∀ receiverRadius : ℝ, ∀ receiverNonnegative : 0 ≤ receiverRadius,
    receiverRadius ≤ factor / 39321600 * ({scales with frequency := frequency} : Scales).length (receiver.1.val + 1) →
    let changed : Scales := {scales with frequency := frequency}
    let original := (prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes).quadrupole receiver.1
    let comparison : MovingPatchFamilySourceComparison 4 :=
      {original with receiverRadius := receiverRadius, receiverRadius_nonnegative := receiverNonnegative}
    let centerState := ‖(fun patch => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time receiver.1 patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time receiver.1) -
      (fun patch => patchCentroid prepared.trajectory.movingFamily.patchMotion time receiver.1 patch -
        quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time receiver.1)‖ / changed.length (receiver.1.val + 1)
    Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖comparison.first.exteriorTaylorCoefficient (Finset.univ.erase receiver.2) comparison.firstReceiver
          receiverRadius (power + 1) time -
        comparison.second.exteriorTaylorCoefficient (Finset.univ.erase receiver.2) comparison.secondReceiver
          receiverRadius (power + 1) time‖) ∧
    (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖comparison.first.exteriorTaylorCoefficient (Finset.univ.erase receiver.2) comparison.firstReceiver
          receiverRadius (power + 1) time -
        comparison.second.exteriorTaylorCoefficient (Finset.univ.erase receiver.2) comparison.secondReceiver
          receiverRadius (power + 1) time‖) ≤
      constant * changed.omega (receiver.1.val + 1) *
        (centerState + (changed.radius (receiver.1.val + 1) ^ 2 / changed.length (receiver.1.val + 1) ^ 2) *
          ∑ patch ∈ Finset.univ.erase receiver.2, (comparison.source patch).spectralDifferenceBudget) := by
  obtain ⟨sourceRadius, sourcePositive, shapeConstant, shapeNonnegative, bound⟩ :=
    exists_uniform_actual_own_virtual_series
  obtain ⟨rawCap, rawPositive, actualShapes⟩ := exists_actual_source_stopped_shape_radius sourcePositive
  refine ⟨sourceRadius, sourcePositive, rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  let centerConstant : ℝ := 64 * 96 * (factor / 800)⁻¹ ^ 3
  let spectralConstant : ℝ := 2 * (shapeConstant * 96 ^ 2 * 96 / Real.pi) * (factor / 800)⁻¹ ^ 4
  refine ⟨centerConstant + spectralConstant, by dsimp only [centerConstant, spectralConstant]; positivity, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive threshold referenceConstant thresholdSmall referenceNonnegative
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    bound scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative factorPositive factorSmall,
    scales.eventually_actual_cascade_source_comparison_geometry amplitudePositive ratioBound alphaPositive
      thresholdSmall referenceNonnegative factorPositive factorSmall (weight := 1) (by norm_num)
      (parameterRadius := 1) (by norm_num)] with frequency frequencyPositive estimate geometry
  intro count orbit sectionTime phase dipoleAngle scaleRoot shapeRadius monitor boundaryConstant prepared path time inside receiver
  let shapes := actualShapes prepared path time inside
  refine ⟨shapes, ?_⟩
  intro receiverRadius receiverNonnegative receiverSmall
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let original := (prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes).quadrupole receiver.1
  let comparison : MovingPatchFamilySourceComparison 4 :=
    {original with receiverRadius := receiverRadius, receiverRadius_nonnegative := receiverNonnegative}
  let centerState := ‖(fun patch => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time receiver.1 patch -
      quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time receiver.1) -
    (fun patch => patchCentroid prepared.trajectory.movingFamily.patchMotion time receiver.1 patch -
      quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time receiver.1)‖ / changed.length (receiver.1.val + 1)
  let epsilon := changed.radius (receiver.1.val + 1) ^ 2 / changed.length (receiver.1.val + 1) ^ 2
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (receiver.1.val + 1)
  have lengthPositive := changed.length_pos (receiver.1.val + 1)
  have separationPositive : 0 < factor / 800 := by positivity
  have actual := estimate count orbit sectionTime phase dipoleAngle prepared path inside shapes receiver
    receiverRadius receiverNonnegative receiverSmall
  dsimp only at actual
  have actualNormalized : Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖comparison.first.exteriorTaylorCoefficient (Finset.univ.erase receiver.2) comparison.firstReceiver
          receiverRadius (power + 1) time -
        comparison.second.exteriorTaylorCoefficient (Finset.univ.erase receiver.2) comparison.secondReceiver
          receiverRadius (power + 1) time‖) ∧
    (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖comparison.first.exteriorTaylorCoefficient (Finset.univ.erase receiver.2) comparison.firstReceiver
          receiverRadius (power + 1) time -
        comparison.second.exteriorTaylorCoefficient (Finset.univ.erase receiver.2) comparison.secondReceiver
          receiverRadius (power + 1) time‖) ≤
      2 * ∑ patch ∈ Finset.univ.erase receiver.2,
        ((comparison.source patch).centerDifferenceEnvelope (factor / 800 * changed.length (receiver.1.val + 1)) 96 +
          (comparison.source patch).centeredShapeDifferenceEnvelope shapeConstant 96) := by
    exact actual
  refine ⟨actualNormalized.1, actualNormalized.2.trans ?_⟩
  have patchBound (patch : Fin 4) (member : patch ∈ Finset.univ.erase receiver.2) :
      ((comparison.source patch).centerDifferenceEnvelope (factor / 800 * changed.length (receiver.1.val + 1)) 96 +
        (comparison.source patch).centeredShapeDifferenceEnvelope shapeConstant 96) / changed.omega (receiver.1.val + 1) ≤
      8 * 96 * (factor / 800)⁻¹ ^ 3 * centerState +
        (shapeConstant * 96 ^ 2 * 96 / Real.pi) * (factor / 800)⁻¹ ^ 4 * epsilon *
          (comparison.source patch).spectralDifferenceBudget := by
    have different : receiver ≠ (receiver.1, patch) := by
      intro same
      exact (Finset.mem_erase.mp member).1 (Prod.mk.inj same).2.symm
    have actualGeometry := geometry count orbit sectionTime phase dipoleAngle
      prepared.toCascadeMaterialPreparedPair path time inside receiver (receiver.1, patch) different
    have distanceIdentity : (factor / 8) * changed.individualInteractionDistance
        (receiver.1.val + 1) (receiver.1.val + 1) = factor / 800 * changed.length (receiver.1.val + 1) := by
      unfold Scales.individualInteractionDistance
      simp only [ite_true]
      ring
    have separated : factor / 800 * changed.length (receiver.1.val + 1) ≤
        ‖(comparison.source patch).secondReceiver - (comparison.source patch).second.center (comparison.source patch).time‖ := by
      have lower := actualGeometry.2.2.1
      rw [distanceIdentity] at lower
      have transferred : 2 * (comparison.source patch).first.radius +
          factor / 800 * changed.length (receiver.1.val + 1) ≤
          ‖(comparison.source patch).secondReceiver - (comparison.source patch).second.center (comparison.source patch).time‖ := lower
      linarith [(comparison.source patch).first.radius_positive.le]
    have mass := prepared.sourceComparison_source_absolute_mass_radius path inside (finProdFinEquiv receiver)
      shapes amplitudePositive frequencyPositive ratioPositive (receiver.1, patch)
    have normalized := (comparison.source patch).centeredDifferenceEnvelopes_normalized_le
      omegaPositive lengthPositive separationPositive shapeNonnegative (by norm_num : (0 : ℝ) ≤ 96) mass separated
    have sourceRadiusIdentity : (comparison.source patch).first.radius = changed.radius (receiver.1.val + 1) := by
      change prepared.referenceWitness.configuration.radius (finProdFinEquiv (receiver.1, patch)) = _
      exact prepared.referenceWitness.radiusIdentity receiver.1 patch
    rw [sourceRadiusIdentity] at normalized
    apply normalized.trans
    apply add_le_add_right
    have displacement := prepared.sourceComparison_own_displacement_le_centered_array path inside shapes receiver patch
    have divided := div_le_div_of_nonneg_right displacement lengthPositive.le
    have stateBound : ‖(comparison.source patch).displacementDifference‖ / changed.length (receiver.1.val + 1) ≤
        2 * centerState := by
      simpa only [mul_div_assoc, centerState] using divided
    have multiplied := mul_le_mul_of_nonneg_left stateBound
      (show 0 ≤ 4 * (96 : ℝ) * (factor / 800)⁻¹ ^ 3 by positivity)
    exact multiplied.trans_eq (by ring)
  have sumBound := Finset.sum_le_sum (fun patch member => patchBound patch member)
  rw [← Finset.sum_div] at sumBound
  have countIdentity : (Finset.univ.erase receiver.2).card = 3 := by simp
  have sumRightIdentity :
      (∑ patch ∈ Finset.univ.erase receiver.2,
        (8 * 96 * (factor / 800)⁻¹ ^ 3 * centerState +
          (shapeConstant * 96 ^ 2 * 96 / Real.pi) * (factor / 800)⁻¹ ^ 4 * epsilon *
            (comparison.source patch).spectralDifferenceBudget)) =
      3 * (8 * 96 * (factor / 800)⁻¹ ^ 3 * centerState) +
        (shapeConstant * 96 ^ 2 * 96 / Real.pi) * (factor / 800)⁻¹ ^ 4 * epsilon *
          ∑ patch ∈ Finset.univ.erase receiver.2, (comparison.source patch).spectralDifferenceBudget := by
    rw [Finset.sum_add_distrib, Finset.sum_const, countIdentity, nsmul_eq_mul, ← Finset.mul_sum]
    norm_num
  rw [sumRightIdentity] at sumBound
  have normalizedBound := mul_le_mul_of_nonneg_left sumBound (by norm_num : (0 : ℝ) ≤ 2)
  rw [← mul_div_assoc] at normalizedBound
  suffices finalBound :
      2 * (∑ patch ∈ Finset.univ.erase receiver.2,
        ((comparison.source patch).centerDifferenceEnvelope (factor / 800 * changed.length (receiver.1.val + 1)) 96 +
          (comparison.source patch).centeredShapeDifferenceEnvelope shapeConstant 96)) / changed.omega (receiver.1.val + 1) ≤
        (centerConstant + spectralConstant) * (centerState + epsilon *
          ∑ patch ∈ Finset.univ.erase receiver.2, (comparison.source patch).spectralDifferenceBudget) by
    exact ((div_le_iff₀ omegaPositive).mp finalBound).trans_eq (by ring)
  apply normalizedBound.trans
  have centerNonnegative : 0 ≤ centerState := by dsimp only [centerState]; positivity
  have epsilonNonnegative : 0 ≤ epsilon := by dsimp only [epsilon]; positivity
  have budgetNonnegative : 0 ≤ ∑ patch ∈ Finset.univ.erase receiver.2,
      (comparison.source patch).spectralDifferenceBudget :=
    Finset.sum_nonneg (fun patch _ => (comparison.source patch).spectralDifferenceBudget_nonnegative)
  have centerCoefficientNonnegative : 0 ≤ centerConstant := by dsimp only [centerConstant]; positivity
  have spectralCoefficientNonnegative : 0 ≤ spectralConstant := by dsimp only [spectralConstant]; positivity
  have centerSlack : 0 ≤ (centerConstant - 48 * 96 * (factor / 800)⁻¹ ^ 3) * centerState := by
    dsimp only [centerConstant]
    have nonnegative : 0 ≤ (factor / 800)⁻¹ ^ 3 * centerState := mul_nonneg (by positivity) centerNonnegative
    nlinarith
  have mixedOne := mul_nonneg centerCoefficientNonnegative (mul_nonneg epsilonNonnegative budgetNonnegative)
  have mixedTwo := mul_nonneg spectralCoefficientNonnegative centerNonnegative
  dsimp only [centerConstant] at centerSlack mixedOne
  dsimp only [spectralConstant] at spectralCoefficientNonnegative mixedTwo
  dsimp only [centerConstant, spectralConstant]
  nlinarith


end EulerNonuniqueness.Paper

