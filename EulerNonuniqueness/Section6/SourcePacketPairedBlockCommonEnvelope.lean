import EulerNonuniqueness.Section6.SourcePacketActualOutgoingBlockCommonEnvelope
import EulerNonuniqueness.Section6.SourcePacketReferenceCoefficientReceiverUniformEnvelope
import EulerNonuniqueness.Section5.CascadeIndividualSourceInputContinuity
import EulerNonuniqueness.Section5.CascadeQuadrupoleForeignClearance
import EulerNonuniqueness.Section6.SourcePacketVectorProjectionBound

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

private theorem block_common_subfamily_vorticity {count : ℕ}
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

private theorem block_common_coefficient_one_eq_strain {count : ℕ}
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
  rw [block_common_subfamily_vorticity family scales densityIdentity source time,
    exteriorVorticityCoefficient_zero_eq_complexStrain] at actual
  exact actual

theorem exists_actual_paired_block_common_envelope :
    ∃ thresholdRadius > (0 : ℝ), thresholdRadius ≤ 1 / 8 ∧ ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdRadius,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant : ℝ),
    0 < factor → factor ≤ 1 / 8 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count,
    receiver.val < source.val →
    ∀ start horizon initialDistance : ℝ, 0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
    512 ≤ initialDistance → initialDistance ≤ ({scales with frequency := frequency} : Scales).omega (source.val + 1) / 16 →
    ∀ direction : ℂ, ‖direction‖ = 1 →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily
    let second := prepared.referenceWitness.trajectory.movingFamily
    let length := changed.length (source.val + 1)
    let distance := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
    ‖firstDipoleSeparation first.patchMotion start source - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation first.patchMotion start source - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter first.patchMotion start source - secondDipoleCenter first.patchMotion start source)).re →
    ‖firstDipoleCenter first.patchMotion start source - secondDipoleCenter first.patchMotion start source‖ ≤ (5 / 4 : ℝ) * length * initialDistance →
    ∀ receiverRadius : ℝ, 0 ≤ receiverRadius → receiverRadius ≤ distance / (100000 * 96) →
    ∀ elapsed ∈ Icc 0 horizon,
    let time := start + elapsed
    let coefficient := fun power : ℕ =>
      (first.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => quadrupoleCenter first.patchMotion current receiver) receiverRadius (power + 1) time -
        (second.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => quadrupoleCenter second.patchMotion current receiver) receiverRadius (power + 1) time
    let strain := vorticityComplexStrain (quadrupoleDensity changed first.patchMotion time source)
        (quadrupoleCenter first.patchMotion time receiver) -
      vorticityComplexStrain (quadrupoleDensity changed second.patchMotion time source)
        (quadrupoleCenter second.patchMotion time receiver)
    let sourceEnvelope := 4 * ‖centroidAsymmetry first.patchMotion time source‖ +
      length * ‖firstDipoleCenter first.patchMotion time source - secondDipoleCenter first.patchMotion time source‖ +
      changed.radius (source.val + 1) ^ 2 + length ^ 2
    Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖coefficient power‖) ∧
      changed.location (receiver.val + 1) ^ 4 * (∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖coefficient power‖) ≤
        constant * changed.circulation (source.val + 1) * sourceEnvelope ∧
      changed.location (receiver.val + 1) ^ 4 * ‖strain‖ ≤ constant * changed.circulation (source.val + 1) * sourceEnvelope ∧
      changed.location (receiver.val + 1) ^ 4 *
          ‖relativeBlockSourceShapeInput changed first.patchMotion prepared.reference receiver source time‖ ≤
        constant * changed.circulation (source.val + 1) * sourceEnvelope := by
  obtain ⟨thresholdRadius, thresholdPositive, thresholdSmall, alternatives⟩ := exists_actual_outgoing_block_common_envelope
  obtain ⟨chartRadius, chartPositive, projection⟩ := exists_reference_strain_vector_projection_bound
  refine ⟨thresholdRadius, thresholdPositive, thresholdSmall, 2000000000, by norm_num, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound
    orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  have sharpPositive : 0 < min chartRadius (1 / 4 : ℝ) := lt_min chartPositive (by norm_num)
  filter_upwards [alternatives scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude
      threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne,
    scales.eventually_reference_coefficient_receiver_uniform_envelope amplitudePositive ratioBound alphaPositive orbit sectionTime
      (thresholdBound.trans thresholdSmall) referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative sharpPositive,
    scales.eventually_cascade_quadrupole_foreign_clearance amplitudePositive ratioBound alphaPositive orbit sectionTime
      (thresholdBound.trans thresholdSmall) referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    eventually_gt_atTop (0 : ℝ)] with frequency alternative reference sharp clearance frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source ordered start horizon initialDistance
    startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper receiverRadius receiverNonnegative receiverSmall elapsed inside
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let time := start + elapsed
  let distance := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
  let firstCoefficient := fun radius power => (first.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
    (fun current => quadrupoleCenter first.patchMotion current receiver) radius (power + 1) time
  let secondCoefficient := fun radius power => (second.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
    (fun current => quadrupoleCenter second.patchMotion current receiver) radius (power + 1) time
  let sourceEnvelope := 4 * ‖centroidAsymmetry first.patchMotion time source‖ +
    changed.length (source.val + 1) * ‖firstDipoleCenter first.patchMotion time source - secondDipoleCenter first.patchMotion time source‖ +
    changed.radius (source.val + 1) ^ 2 + changed.length (source.val + 1) ^ 2
  have timeInside : time ∈ Icc 0 path.stop :=
    ⟨by change 0 ≤ start + elapsed; linarith only [startNonnegative, inside.1],
      by change start + elapsed ≤ path.stop; linarith only [endBound, inside.2]⟩
  have different : receiver ≠ source := by intro equality; have := congrArg Fin.val equality; omega
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have circulationNonnegative := (changed.circulation_pos frequencyPositive ratioPositive (source.val + 1)).le
  have lengthPositive := changed.length_pos (source.val + 1)
  have paired (radius : ℝ) (nonnegative : 0 ≤ radius) (small : radius ≤ distance / (100000 * 96)) :
      Summable (fun power => (96 : ℝ) ^ (power + 1) * ‖firstCoefficient radius power - secondCoefficient radius power‖) ∧
        changed.location (receiver.val + 1) ^ 4 *
            (∑' power, (96 : ℝ) ^ (power + 1) * ‖firstCoefficient radius power - secondCoefficient radius power‖) ≤
          2000000000 * changed.circulation (source.val + 1) * sourceEnvelope := by
    have alt := alternative count phase dipoleAngle prepared path receiver source ordered start horizon initialDistance
      startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
      firstInitial secondInitial initialProjection initialUpper radius nonnegative small elapsed inside
    have ref := reference count phase dipoleAngle prepared path receiver source ordered radius nonnegative small none time timeInside
    have pointwise (power : ℕ) : (96 : ℝ) ^ (power + 1) * ‖firstCoefficient radius power - secondCoefficient radius power‖ ≤
        (96 : ℝ) ^ (power + 1) * ‖firstCoefficient radius power‖ + (96 : ℝ) ^ (power + 1) * ‖secondCoefficient radius power‖ :=
      (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)).trans_eq (mul_add _ _ _)
    have majorant := alt.1.add ref.1
    have summable : Summable (fun power => (96 : ℝ) ^ (power + 1) *
        ‖firstCoefficient radius power - secondCoefficient radius power‖) :=
      Summable.of_nonneg_of_le (fun power => mul_nonneg (by positivity) (norm_nonneg _)) pointwise majorant
    have comparison := summable.tsum_le_tsum pointwise majorant
    rw [alt.1.tsum_add ref.1] at comparison
    have scaled := mul_le_mul_of_nonneg_left comparison (pow_nonneg (changed.location_pos (receiver.val + 1)).le 4)
    rw [mul_add] at scaled
    refine ⟨summable, scaled.trans ((add_le_add alt.2 ref.2).trans ?_)⟩
    dsimp only [sourceEnvelope]
    have firstNonnegative : 0 ≤ changed.circulation (source.val + 1) *
        (4 * ‖centroidAsymmetry first.patchMotion time source‖ + changed.length (source.val + 1) *
          ‖firstDipoleCenter first.patchMotion time source - secondDipoleCenter first.patchMotion time source‖ + changed.radius (source.val + 1) ^ 2) := by
      apply mul_nonneg circulationNonnegative
      positivity
    nlinarith only [firstNonnegative, mul_nonneg circulationNonnegative (sq_nonneg (changed.length (source.val + 1)))]
  have distancePositive : 0 < distance / 8 := div_pos
    (changed.location_distance_pos (fun equality => different (Fin.ext (Nat.add_right_cancel equality)))) (by norm_num)
  have zeroData := paired 0 (by norm_num) (by dsimp only [distance]; positivity)
  have member : source ∈ Finset.univ.erase receiver := Finset.mem_erase.mpr ⟨different.symm, Finset.mem_univ _⟩
  have gaps := clearance count phase dipoleAngle prepared path time timeInside receiver
  have firstIdentity := block_common_coefficient_one_eq_strain first changed prepared.densityIdentity source
    (fun current => quadrupoleCenter first.patchMotion current receiver) time distancePositive (gaps.2 source member)
  have secondIdentity := block_common_coefficient_one_eq_strain second changed prepared.referenceWitness.densityIdentity source
    (fun current => quadrupoleCenter second.patchMotion current receiver) time distancePositive (gaps.1 source member)
  have term := zeroData.1.le_tsum 0 (fun power _ => mul_nonneg (by positivity) (norm_nonneg _))
  simp only [zero_add, pow_one, firstCoefficient, secondCoefficient, firstIdentity, secondIdentity] at term
  have scaledTerm := (mul_le_mul_of_nonneg_left term (pow_nonneg (changed.location_pos (receiver.val + 1)).le 4)).trans zeroData.2
  have defect := sharp prepared time ⟨timeInside.1, timeInside.2.trans path.stopBound⟩ receiver
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
  change ‖relativeBlockSourceShapeInput changed first.patchMotion prepared.reference receiver source time‖ ≤ 5 * ‖_‖ at projected
  rw [prepared.referenceIdentity] at projected
  have projectedScaled := mul_le_mul_of_nonneg_left projected (pow_nonneg (changed.location_pos (receiver.val + 1)).le 4)
  have strainNonnegative : 0 ≤ changed.location (receiver.val + 1) ^ 4 *
      ‖vorticityComplexStrain (quadrupoleDensity changed first.patchMotion time source) (quadrupoleCenter first.patchMotion time receiver) -
        vorticityComplexStrain (quadrupoleDensity changed second.patchMotion time source) (quadrupoleCenter second.patchMotion time receiver)‖ := by positivity
  refine ⟨(paired receiverRadius receiverNonnegative receiverSmall).1,
    (paired receiverRadius receiverNonnegative receiverSmall).2, ?_, ?_⟩
  · change changed.location (receiver.val + 1) ^ 4 *
        ‖vorticityComplexStrain (quadrupoleDensity changed first.patchMotion time source) (quadrupoleCenter first.patchMotion time receiver) -
          vorticityComplexStrain (quadrupoleDensity changed second.patchMotion time source) (quadrupoleCenter second.patchMotion time receiver)‖ ≤
      2000000000 * changed.circulation (source.val + 1) * sourceEnvelope
    nlinarith only [scaledTerm, strainNonnegative]
  · rw [prepared.referenceIdentity]
    change changed.location (receiver.val + 1) ^ 4 *
        ‖relativeBlockSourceShapeInput changed first.patchMotion second.patchMotion receiver source time‖ ≤
      2000000000 * changed.circulation (source.val + 1) * sourceEnvelope
    change changed.location (receiver.val + 1) ^ 4 *
        ‖relativeBlockSourceShapeInput changed first.patchMotion second.patchMotion receiver source time‖ ≤
      changed.location (receiver.val + 1) ^ 4 * (5 *
        ‖vorticityComplexStrain (quadrupoleDensity changed first.patchMotion time source) (quadrupoleCenter first.patchMotion time receiver) -
          vorticityComplexStrain (quadrupoleDensity changed second.patchMotion time source) (quadrupoleCenter second.patchMotion time receiver)‖) at projectedScaled
    nlinarith only [scaledTerm, projectedScaled, strainNonnegative]

end EulerNonuniqueness.Paper
