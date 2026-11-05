import EulerNonuniqueness.Section5.CascadeActualMacroCoefficientSeriesAction
import EulerNonuniqueness.Section6.SourcePacketForeignVectorCoarse
import EulerNonuniqueness.Section4.ReferenceForeignStrainIdentity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem quadrupoleSubfamily_field_identity {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityIdentity : ∀ index patch, family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (source : Fin count) (time : ℝ) :
    (family.quadrupoleSubfamily source).subfamilyVorticity Finset.univ time =
      quadrupoleDensity scales family.patchMotion time source := by
  funext position
  change (∑ patch : Fin 4, family.patchVorticity time (finProdFinEquiv (source, patch)) position) = _
  unfold quadrupoleDensity
  apply Finset.sum_congr rfl
  intro patch member
  exact congrFun (family.patchDensity_eq scales densityIdentity time source patch).symm position

private theorem quadrupoleSubfamily_coefficient_one_eq_literal_strain {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityIdentity : ∀ index patch, family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (source : Fin count) (center : ℝ → ℂ) (radius time : ℝ) {distance : ℝ}
    (distancePositive : 0 < distance)
    (separated : ∀ patch position, position ∈ family.patchMotion.domain time source patch → distance ≤ ‖center time - position‖) :
    (family.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ center radius 1 time =
      vorticityComplexStrain (quadrupoleDensity scales family.patchMotion time source) (center time) := by
  have actual := (family.quadrupoleSubfamily source).exteriorTaylorCoefficient_eq_vorticityCoefficient
    Finset.univ center radius time 0 distancePositive (fun patch _ position member => separated patch position member)
  rw [quadrupoleSubfamily_field_identity family scales densityIdentity source time,
    exteriorVorticityCoefficient_zero_eq_complexStrain] at actual
  exact actual

private theorem Scales.coarser_macroPolynomial_masked_action {count : ℕ} (scales : Scales)
    (frequencyOne : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {constant : ℝ} (constantNonnegative : 0 ≤ constant) (states : Fin count → ℝ)
    (statesNonnegative : ∀ source, 0 ≤ states source) (receiver : Fin count) :
    scales.location (receiver.val + 1) ^ 4 *
        (∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.val),
          scales.macroCoefficientFeedbackPolynomial constant 1 (receiver.val + 1) (source.val + 1)
            (states receiver) (states source)) ≤
      (1000000000 * (constant + 1)) * (216360000 * scales.hessian + 576 * scales.strain) *
        ‖fun source : Fin count => if source.val ≤ receiver.val then scales.location (source.val + 1) ^ 4 * states source else 0‖ := by
  let selected := Finset.univ.filter (fun source : Fin count => source.val < receiver.val)
  let masked := fun source : Fin count => if source.val ≤ receiver.val then states source else 0
  have maskedNonnegative (source : Fin count) : 0 ≤ masked source := by
    dsimp only [masked]
    split
    · exact statesNonnegative source
    · exact le_rfl
  have subset : selected ⊆ Finset.univ.erase receiver := by
    intro source member
    have below := (Finset.mem_filter.mp member).2
    exact Finset.mem_erase.mpr ⟨by intro same; subst source; omega, Finset.mem_univ _⟩
  have receiverIdentity : masked receiver = states receiver := by simp only [masked, le_refl, ite_true]
  have sourceIdentity (source : Fin count) (member : source ∈ selected) : masked source = states source := by
    exact if_pos (Nat.le_of_lt (Finset.mem_filter.mp member).2)
  have sumIdentity : (∑ source ∈ selected,
      scales.macroCoefficientFeedbackPolynomial constant 1 (receiver.val + 1) (source.val + 1)
        (masked receiver) (masked source)) =
      ∑ source ∈ selected,
        scales.macroCoefficientFeedbackPolynomial constant 1 (receiver.val + 1) (source.val + 1)
          (states receiver) (states source) := by
    apply Finset.sum_congr rfl
    intro source member
    rw [receiverIdentity, sourceIdentity source member]
  have arrayIdentity : (fun source : Fin count => scales.location (source.val + 1) ^ 4 * masked source) =
      (fun source : Fin count => if source.val ≤ receiver.val then scales.location (source.val + 1) ^ 4 * states source else 0) := by
    funext source
    by_cases below : source.val ≤ receiver.val <;> simp only [masked, below, ite_true, ite_false, mul_zero]
  have actual := scales.macroCoefficientFeedbackPolynomial_weighted_action_le frequencyOne ratioBound alphaPositive
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1) constantNonnegative (by norm_num : (0 : ℝ) ≤ 1)
    masked maskedNonnegative receiver selected subset
  rw [sumIdentity, arrayIdentity] at actual
  simpa only [mul_one] using actual

theorem exists_uniform_actual_coarser_leading_macro_feedback :
    ∃ rawCap > (0 : ℝ), ∃ chartRadius > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < factor → factor ≤ 1 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ time ∈ Icc 0 path.stop, ∀ receiver : Fin count,
    positiveHalfDiagonal prepared.reference time receiver ≠ 0 →
    negativeHalfDiagonal prepared.reference time receiver ≠ 0 →
    |(pointShapeChart (positiveHalfDiagonal prepared.reference time receiver)
        (negativeHalfDiagonal prepared.reference time receiver)).1| +
      |(pointShapeChart (positiveHalfDiagonal prepared.reference time receiver)
        (negativeHalfDiagonal prepared.reference time receiver)).2| ≤ chartRadius →
    let changed : Scales := {scales with frequency := frequency}
    ‖∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.val),
      relativeBlockSourceShapeInput changed prepared.trajectory.movingFamily.patchMotion prepared.reference receiver source time‖ ≤
      (constant / changed.location (receiver.val + 1) ^ 4) *
        (216360000 * changed.hessian + 576 * changed.strain) *
          ‖fun source : Fin count => if source.val ≤ receiver.val then
            changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source else 0‖ := by
  obtain ⟨sourceRadius, sourcePositive, constant, constantNonnegative, seriesFactory⟩ :=
    exists_uniform_actual_foreign_quadrupole_fixed_macro_virtual_series
  obtain ⟨rawCap, rawPositive, shapeFactory⟩ := exists_actual_source_stopped_shape_radius sourcePositive
  obtain ⟨chartRadius, chartPositive, projection⟩ := exists_reference_strain_vector_projection_bound
  refine ⟨rawCap, rawPositive, chartRadius, chartPositive, 5 * (1000000000 * (constant + 1)), by positivity, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  filter_upwards [seriesFactory 1 (by norm_num) scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_macro_follower_centroid_clearance amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_quadrupole_foreign_clearance amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    eventually_ge_atTop (1 : ℝ),
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1)]
    with frequency estimates alignment centroidClearance domainClearance frequencyOne radii lengths
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver positiveNonzero negativeNonzero chartSmall
  dsimp only
  rw [prepared.referenceIdentity] at positiveNonzero negativeNonzero chartSmall ⊢
  let changed : Scales := {scales with frequency := frequency}
  let shapes := shapeFactory prepared path time inside
  let original := prepared.sourceComparison path inside (finProdFinEquiv (receiver, 0)) shapes
  let comparison := original.withQuadrupoleReceivers receiver 0 (by norm_num)
  let first := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let second := prepared.trajectory.movingFamily.patchMotion
  let selected := Finset.univ.filter (fun source : Fin count => source.val < receiver.val)
  have selectedSubset : selected ⊆ Finset.univ.erase receiver := by
    intro source member
    have below := (Finset.mem_filter.mp member).2
    exact Finset.mem_erase.mpr ⟨by intro same; subst source; omega, Finset.mem_univ _⟩
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 := ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
  have secondCenters (source : Fin count) (patch : Fin 4) : ((comparison.quadrupole source).second.patch patch).center time =
      patchCentroid second time source patch :=
    prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside source patch
  have stateIdentity (source : Fin count) : (comparison.quadrupole source).relativeMacroState
      (quadrupoleCenter first time source) (quadrupoleCenter second time source) (changed.location (source.val + 1)) =
      prepared.macroSourceState time source := by
    rw [MovingPatchFamilySourceComparison.withQuadrupoleReceivers_relativeMacroState]
    exact prepared.sourceComparison_relativeMacroState path inside (finProdFinEquiv (receiver, 0)) shapes source
  have sourceEstimates (source : Fin count) (member : source ∈ selected) := by
    have different : receiver ≠ source := Ne.symm (Finset.mem_erase.mp (selectedSubset member)).1
    have geometry := alignment count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside (receiver, 0) source different
    have actual := estimates count phase dipoleAngle prepared path inside shapes receiver source different
      (changed.location (source.val + 1) / 100)
      (div_nonneg (changed.location_pos _).le (by norm_num)) le_rfl geometry.2.2.1 geometry.2.2.2
      0 (by norm_num) (by have positive := changed.location_pos (receiver.val + 1); positivity)
    exact actual
  have polynomialBound (source : Fin count) (member : source ∈ selected) :
      (comparison.quadrupole source).quadrupolePointDifferenceEnvelope (changed.circulation (source.val + 1))
          (quadrupoleCenter first time source) (quadrupoleCenter second time source)
          (changed.location (source.val + 1) / 100)
          (|changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 8) 1 +
        2 * (∑ patch : Fin 4,
          (((comparison.quadrupole source).source patch).centroidCorrectionCenterEnvelope
              (|changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 8) 1 +
            ((comparison.quadrupole source).source patch).centeredShapeDifferenceEnvelope constant 1)) ≤
      changed.macroCoefficientFeedbackPolynomial constant 1 (receiver.val + 1) (source.val + 1)
        (prepared.macroSourceState time receiver) (prepared.macroSourceState time source) := by
    have different : receiver ≠ source := Ne.symm (Finset.mem_erase.mp (selectedSubset member)).1
    have differentIndices : receiver.val + 1 ≠ source.val + 1 := fun equality => different (Fin.ext (Nat.add_right_cancel equality))
    have geometry := alignment count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside (receiver, 0) source different
    have radiusBound (patch : Fin 4) : ((comparison.quadrupole source).source patch).first.radius ≤ changed.location (source.val + 1) := by
      have identity : ((comparison.quadrupole source).source patch).first.radius = changed.radius (source.val + 1) := prepared.referenceWitness.radiusIdentity source patch
      rw [identity]
      exact (radii (source.val + 1)).le.trans (by simpa only [one_mul] using (lengths (source.val + 1)).le)
    have referencePositions (patch : Fin 4) : ‖((comparison.quadrupole source).second.patch patch).center time -
        quadrupoleCenter second time source‖ ≤ changed.location (source.val + 1) := by
      rw [secondCenters]
      linarith only [geometry.2.2.2 patch, changed.location_pos (source.val + 1)]
    have actual := (comparison.quadrupole source).quadrupole_coefficient_macro_state_bound
      (distance := |changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 8)
      (quadrupoleCenter first time source) (quadrupoleCenter second time source)
      (changed.circulation_pos frequencyPositive ratioPositive _).le constantNonnegative
      (div_nonneg (changed.location_pos _).le (by norm_num))
      (show changed.location (source.val + 1) / 100 ≤ changed.location (source.val + 1) by linarith only [changed.location_pos (source.val + 1)])
      (div_pos (changed.location_distance_pos differentIndices) (by norm_num)) (by norm_num : (0 : ℝ) ≤ 1)
      (changed.location_pos _).le (changed.location_pos _) (prepared.macroSourceState_nonnegative time receiver)
      (by change 8 * 1 * 0 / _ ≤ (1 / 2 : ℝ); norm_num)
      referencePositions (prepared.macroSourceState_center_difference time receiver)
      (fun patch => prepared.sourceComparison_quadrupole_mass_budget path inside (finProdFinEquiv (receiver, 0)) shapes
        amplitudePositive frequencyPositive ratioPositive source patch) radiusBound
      (fun patch => by
        change |changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 8 ≤
          ‖quadrupoleCenter second time receiver - ((comparison.quadrupole source).second.patch patch).center time‖
        rw [secondCenters]
        exact centroidClearance count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside receiver source different patch)
    dsimp only at actual
    rw [stateIdentity] at actual
    exact actual
  have sourceVectorBound (source : Fin count) (member : source ∈ selected) :
      ‖relativeBlockSourceShapeInput changed second first receiver source time‖ ≤
        5 * changed.macroCoefficientFeedbackPolynomial constant 1 (receiver.val + 1) (source.val + 1)
          (prepared.macroSourceState time receiver) (prepared.macroSourceState time source) := by
    have different : receiver.val + 1 ≠ source.val + 1 := fun equality =>
      (Finset.mem_erase.mp (selectedSubset member)).1 (Fin.ext (Nat.add_right_cancel equality).symm)
    have distancePositive := div_pos (changed.location_distance_pos different) (by norm_num : (0 : ℝ) < 8)
    have gaps := domainClearance count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside receiver
    have firstZero : (comparison.quadrupole source).first.exteriorTaylorCoefficient Finset.univ
        comparison.firstReceiver 0 1 time =
        vorticityComplexStrain (quadrupoleDensity changed first time source) (quadrupoleCenter first time receiver) :=
      quadrupoleSubfamily_coefficient_one_eq_literal_strain prepared.referenceWitness.trajectory.movingFamily changed
        prepared.referenceWitness.densityIdentity source comparison.firstReceiver 0 time distancePositive
        (gaps.1 source (selectedSubset member))
    have secondZero : (comparison.quadrupole source).second.exteriorTaylorCoefficient Finset.univ
        comparison.secondReceiver 0 1 time =
        vorticityComplexStrain (quadrupoleDensity changed second time source) (quadrupoleCenter second time receiver) :=
      quadrupoleSubfamily_coefficient_one_eq_literal_strain prepared.trajectory.movingFamily changed
        prepared.densityIdentity source comparison.secondReceiver 0 time distancePositive
        (gaps.2 source (selectedSubset member))
    have actual := sourceEstimates source member
    have zeroBound := actual.1.le_tsum 0 (fun power _ => mul_nonneg (by positivity) (norm_nonneg _))
    simp only [zero_add, pow_one, one_mul] at zeroBound
    have coefficientBound := zeroBound.trans (actual.2.trans (polynomialBound source member))
    have projected := projection (positiveHalfDiagonal first time receiver) (negativeHalfDiagonal first time receiver)
      (vorticityComplexStrain (quadrupoleDensity changed second time source) (quadrupoleCenter second time receiver) -
        vorticityComplexStrain (quadrupoleDensity changed first time source) (quadrupoleCenter first time receiver))
      positiveNonzero negativeNonzero chartSmall
    change ‖relativeBlockSourceShapeInput changed second first receiver source time‖ ≤ _ at projected
    rw [← secondZero, ← firstZero, norm_sub_rev] at projected
    exact projected.trans (mul_le_mul_of_nonneg_left coefficientBound (by norm_num : (0 : ℝ) ≤ 5))
  have vectorBound := (norm_sum_le selected (fun source => relativeBlockSourceShapeInput changed second first receiver source time)).trans
    (Finset.sum_le_sum (fun source member => sourceVectorBound source member))
  rw [← Finset.mul_sum] at vectorBound
  have weighted := mul_le_mul_of_nonneg_left vectorBound (pow_nonneg (changed.location_pos (receiver.val + 1)).le 4)
  have row := changed.coarser_macroPolynomial_masked_action frequencyOne ratioBound alphaPositive constantNonnegative
    (prepared.macroSourceState time) (prepared.macroSourceState_nonnegative time) receiver
  have combined := weighted.trans (by
    have actual := mul_le_mul_of_nonneg_left row (by norm_num : (0 : ℝ) ≤ 5)
    convert actual using 1
    ring)
  have denominatorPositive := pow_pos (changed.location_pos (receiver.val + 1)) 4
  calc
    _ ≤ (5 * (1000000000 * (constant + 1)) * (216360000 * changed.hessian + 576 * changed.strain) *
        ‖fun source : Fin count => if source.val ≤ receiver.val then changed.location (source.val + 1) ^ 4 *
          prepared.macroSourceState time source else 0‖) / changed.location (receiver.val + 1) ^ 4 :=
      (le_div_iff₀ denominatorPositive).mpr (by simpa only [mul_comm, mul_left_comm, mul_assoc] using combined)
    _ = _ := by ring

end EulerNonuniqueness.Paper
