import EulerNonuniqueness.Section6.SourcePacketPairedBlockCenterArbitraryWeightBudget
import EulerNonuniqueness.Section5.CascadeIndividualSourceInputContinuity
import EulerNonuniqueness.Section6.SourcePacketVectorProjectionBound

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

private theorem leading_budget_subfamily_vorticity {count : ℕ}
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

private theorem leading_budget_coefficient_one_eq_strain {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityIdentity : ∀ index patch, family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (source : Fin count) (center : ℝ → ℂ) (time : ℝ) {distance : ℝ}
    (distancePositive : 0 < distance)
    (separated : ∀ patch position, position ∈ family.patchMotion.domain time source patch → distance ≤ ‖center time - position‖) :
    (family.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ center 0 1 time =
      vorticityComplexStrain (quadrupoleDensity scales family.patchMotion time source) (center time) := by
  have actual := (family.quadrupoleSubfamily source).exteriorTaylorCoefficient_eq_vorticityCoefficient
    Finset.univ center 0 time 0 distancePositive (fun patch _ position member => separated patch position member)
  rw [leading_budget_subfamily_vorticity family scales densityIdentity source time,
    exteriorVorticityCoefficient_zero_eq_complexStrain] at actual
  exact actual

private theorem leading_budget_window_translation (input : ℝ → ℝ) (weight start horizon : ℝ) :
    (∫ time in start..start + horizon, Real.exp (-weight * time) * input time) =
      Real.exp (-weight * start) *
        ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * input (start + elapsed) := by
  have shift := intervalIntegral.integral_comp_add_left
    (f := fun time => Real.exp (-weight * time) * input time) (a := 0) (b := horizon) start
  rw [add_zero] at shift
  rw [← shift, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro elapsed _
  dsimp only
  rw [show -weight * (start + elapsed) = -weight * start + -weight * elapsed by ring, Real.exp_add]
  ring

theorem exists_actual_paired_leading_arbitrary_weight_budget :
    ∃ thresholdRadius > (0 : ℝ), thresholdRadius ≤ 1 / 8 ∧ ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdRadius,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant : ℝ),
    0 < factor → factor ≤ 1 / 8 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver drive source : Fin count,
    receiver.val ≤ drive.val → drive.val < source.val →
    ∀ start horizon initialDistance : ℝ, 0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
    512 ≤ initialDistance → initialDistance ≤ ({scales with frequency := frequency} : Scales).omega (source.val + 1) / 16 →
    ∀ direction : ℂ, ‖direction‖ = 1 →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.reference
    let length := changed.length (source.val + 1)
    let distance := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
    ‖firstDipoleSeparation first start source - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation first start source - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter first start source - secondDipoleCenter first start source)).re →
    ‖firstDipoleCenter first start source - secondDipoleCenter first start source‖ ≤
      (5 / 4 : ℝ) * length * initialDistance →
    ∀ weight : ℝ, changed.omega (drive.val + 1) ≤ weight →
    let input := relativeBlockSourceShapeInput changed first second receiver source
    let cost := changed.circulation (source.val + 1) ^ 2 / (weight ^ 2 * distance ^ 4) +
      (1 + initialDistance) * changed.circulation (source.val + 1) * length ^ 2 / (weight * distance ^ 4) +
      changed.circulation (source.val + 1) * ‖centroidAsymmetry first start source‖ / (weight * distance ^ 3)
    ContinuousOn input (Icc 0 path.stop) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * ‖input time‖) volume 0 (start + horizon) ∧
    IntervalIntegrable (fun elapsed => Real.exp (-weight * elapsed) * ‖input (start + elapsed)‖) volume 0 horizon ∧
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * ‖input (start + elapsed)‖) ≤ constant * cost ∧
    (∫ time in (0 : ℝ)..start + horizon, Real.exp (-weight * time) * ‖input time‖) ≤
      (∫ time in (0 : ℝ)..start, Real.exp (-weight * time) * ‖input time‖) +
        Real.exp (-weight * start) * (constant * cost) := by
  obtain ⟨thresholdRadius, thresholdPositive, thresholdEighth, blockConstant, blockNonnegative, blocks⟩ :=
    exists_actual_paired_blockcenter_source_arbitrary_weight_budget
  obtain ⟨chartRadius, chartPositive, projection⟩ := exists_reference_strain_vector_projection_bound
  refine ⟨thresholdRadius, thresholdPositive, thresholdEighth, (5 / 96 : ℝ) * blockConstant, by positivity, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound
    orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne
  have thresholdSmall := thresholdBound.trans thresholdEighth
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  have sharpPositive : 0 < min chartRadius (1 / 4 : ℝ) := lt_min chartPositive (by norm_num)
  filter_upwards [blocks scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude
      threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne,
    scales.eventually_cascade_individual_source_input_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative sharpPositive,
    scales.eventually_cascade_quadrupole_foreign_clearance amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne]
    with frequency blockEstimate continuity sharp clearance
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver drive source receiverBefore driveBefore
    start horizon initialDistance startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper weight weightLarge
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let distance := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
  let input := relativeBlockSourceShapeInput changed first.patchMotion prepared.reference receiver source
  let coefficient := fun power time =>
    (first.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
        (fun current => quadrupoleCenter first.patchMotion current receiver) 0 (power + 1) time -
      (second.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
        (fun current => quadrupoleCenter second.patchMotion current receiver) 0 (power + 1) time
  let series := fun time => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖coefficient power time‖
  let cost := changed.circulation (source.val + 1) ^ 2 / (weight ^ 2 * distance ^ 4) +
    (1 + initialDistance) * changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 / (weight * distance ^ 4) +
    changed.circulation (source.val + 1) * ‖centroidAsymmetry first.patchMotion start source‖ / (weight * distance ^ 3)
  have different : receiver ≠ source := by intro equality; have := congrArg Fin.val equality; omega
  have member : source ∈ Finset.univ.erase receiver := Finset.mem_erase.mpr ⟨different.symm, Finset.mem_univ _⟩
  have distancePositive : 0 < distance / 8 := div_pos
    (changed.location_distance_pos (fun equality => different (Fin.ext (Nat.add_right_cancel equality)))) (by norm_num)
  have blockData := blockEstimate count phase dipoleAngle prepared path receiver drive source receiverBefore driveBefore
    start horizon initialDistance startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
    firstInitial secondInitial initialProjection initialUpper 0 (by norm_num) (by positivity) weight weightLarge
  dsimp only at blockData
  have inputContinuous : ContinuousOn input (Icc 0 path.stop) := continuity count phase dipoleAngle prepared path receiver source different
  have pointwise (time : ℝ) (inside : time ∈ Icc 0 path.stop) : ‖input time‖ ≤ (5 / 96 : ℝ) * series time := by
    have gaps := clearance count phase dipoleAngle prepared path time inside receiver
    have firstIdentity := leading_budget_coefficient_one_eq_strain first changed prepared.densityIdentity source
      (fun current => quadrupoleCenter first.patchMotion current receiver) time distancePositive (gaps.2 source member)
    have secondIdentity := leading_budget_coefficient_one_eq_strain second changed prepared.referenceWitness.densityIdentity source
      (fun current => quadrupoleCenter second.patchMotion current receiver) time distancePositive (gaps.1 source member)
    have termBound := ((blockData.2.1 time inside).le_tsum 0
      (fun power _ => mul_nonneg (by positivity) (norm_nonneg _)))
    change (96 : ℝ) ^ (0 + 1) * ‖coefficient 0 time‖ ≤ series time at termBound
    simp only [zero_add, pow_one, coefficient, firstIdentity, secondIdentity] at termBound
    have defect := sharp prepared time ⟨inside.1, inside.2.trans path.stopBound⟩ receiver
    have shapeSmall : |unstableShape prepared.reference time receiver| + |stableShape prepared.reference time receiver| ≤
        min chartRadius (1 / 4 : ℝ) := by
      linarith only [defect, abs_nonneg (diagonalDifference prepared.reference time receiver / changed.length (receiver.val + 1) ^ 2 - 1)]
    have upper := paper_shape_ratio_im_pos_of_small prepared.reference time receiver (shapeSmall.trans (min_le_right _ _))
    have positiveNonzero : positiveHalfDiagonal prepared.reference time receiver ≠ 0 := by
      intro zero
      simp only [zero, div_zero, Complex.zero_im, lt_self_iff_false] at upper
    have negativeNonzero : negativeHalfDiagonal prepared.reference time receiver ≠ 0 := by
      intro zero
      simp only [zero, zero_div, Complex.zero_im, lt_self_iff_false] at upper
    have chartSmall : |(pointShapeChart (positiveHalfDiagonal prepared.reference time receiver)
        (negativeHalfDiagonal prepared.reference time receiver)).1| +
        |(pointShapeChart (positiveHalfDiagonal prepared.reference time receiver)
          (negativeHalfDiagonal prepared.reference time receiver)).2| ≤ chartRadius := by
      rw [pointShapeChart_eq_paper_shape_of_upper prepared.reference time receiver upper]
      exact shapeSmall.trans (min_le_left _ _)
    have projected := projection (positiveHalfDiagonal prepared.reference time receiver) (negativeHalfDiagonal prepared.reference time receiver)
      (vorticityComplexStrain (quadrupoleDensity changed first.patchMotion time source) (quadrupoleCenter first.patchMotion time receiver) -
        vorticityComplexStrain (quadrupoleDensity changed prepared.reference time source) (quadrupoleCenter prepared.reference time receiver))
      positiveNonzero negativeNonzero chartSmall
    change ‖input time‖ ≤ 5 * ‖_‖ at projected
    rw [prepared.referenceIdentity] at projected
    nlinarith only [projected, termBound]
  have originalContinuous : ContinuousOn (fun time => Real.exp (-weight * time) * ‖input time‖) (Icc 0 path.stop) :=
    (by fun_prop : Continuous (fun time : ℝ => Real.exp (-weight * time))).continuousOn.mul inputContinuous.norm
  have originalIntegrable := (originalContinuous.mono (Icc_subset_Icc le_rfl endBound)).intervalIntegrable_of_Icc
    (μ := volume) (add_nonneg startNonnegative horizonNonnegative)
  have timeRange (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : start + elapsed ∈ Icc 0 path.stop :=
    ⟨by linarith only [startNonnegative, inside.1], by linarith only [endBound, inside.2]⟩
  have windowContinuous : ContinuousOn (fun elapsed => Real.exp (-weight * elapsed) * ‖input (start + elapsed)‖) (Icc 0 horizon) :=
    (by fun_prop : Continuous (fun elapsed : ℝ => Real.exp (-weight * elapsed))).continuousOn.mul
      (inputContinuous.comp (continuous_const.add continuous_id).continuousOn timeRange).norm
  have windowIntegrable := windowContinuous.intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  have comparison := intervalIntegral.integral_mono_on horizonNonnegative windowIntegrable (blockData.2.2.2.2.1.const_mul (5 / 96 : ℝ))
    (fun elapsed inside => by
      convert mul_le_mul_of_nonneg_left (pointwise _ (timeRange elapsed inside)) (Real.exp_pos (-weight * elapsed)).le using 1; ring)
  rw [intervalIntegral.integral_const_mul] at comparison
  have windowBound : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * ‖input (start + elapsed)‖) ≤
      ((5 / 96 : ℝ) * blockConstant) * cost := by
    exact comparison.trans ((mul_le_mul_of_nonneg_left blockData.2.2.2.2.2.1 (by norm_num : (0 : ℝ) ≤ 5 / 96)).trans_eq (by ring))
  have startBound : start ≤ path.stop := by linarith only [endBound, horizonNonnegative]
  have prefixIntegrable := (originalContinuous.mono (Icc_subset_Icc le_rfl startBound)).intervalIntegrable_of_Icc
    (μ := volume) startNonnegative
  have physicalWindowIntegrable := (originalContinuous.mono (Icc_subset_Icc startNonnegative endBound)).intervalIntegrable_of_Icc
    (μ := volume) (show start ≤ start + horizon by linarith only [horizonNonnegative])
  refine ⟨inputContinuous, originalIntegrable, windowIntegrable, windowBound, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals prefixIntegrable physicalWindowIntegrable,
    leading_budget_window_translation (fun time => ‖input time‖) weight start horizon]
  exact add_le_add_left (mul_le_mul_of_nonneg_left windowBound (Real.exp_pos _).le) _

end EulerNonuniqueness.Paper
