import EulerNonuniqueness.Section5.CascadeIncomingSourceBlockReturn
import EulerNonuniqueness.Section5.CascadeReferenceSharpDefect
import EulerNonuniqueness.Section5.CascadeQuadrupoleForeignClearance
import EulerNonuniqueness.Section6.PaperRelativeLeadingStrainSum
import EulerNonuniqueness.Section6.SourcePacketVectorProjectionBound

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem incoming_subfamily_vorticity_identity {count : ℕ}
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

private theorem incoming_coefficient_one_eq_literal_strain {count : ℕ}
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
  rw [incoming_subfamily_vorticity_identity family scales densityIdentity source time,
    exteriorVorticityCoefficient_zero_eq_complexStrain] at actual
  exact actual

theorem exists_uniform_actual_incoming_source_leading_return :
    ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < factor → factor ≤ 1 / 8 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ receiver source : Fin count, receiver.val < source.val → source.val + 1 < count →
    ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time source| ≤ 1 / 2) →
    ∀ time ∈ Icc 0 finish,
    let changed : Scales := {scales with frequency := frequency}
    let alternative := prepared.trajectory.movingFamily.patchMotion
    let reference := prepared.reference
    let gap := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
    let length := changed.length (source.val + 1)
    let state := prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed alternative reference source time‖ +
      ‖quadrupoleCenter alternative time source - quadrupoleCenter reference time source‖ /
        changed.location (source.val + 1) + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    let budget := constant * (changed.circulation (source.val + 1) * length ^ 2 / gap ^ 4 *
      (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1)) * state +
        changed.circulation (source.val + 1) * length ^ 2 / gap ^ 5 *
          ‖quadrupoleCenter alternative time receiver - quadrupoleCenter reference time receiver‖)
    ‖vorticityComplexStrain (quadrupoleDensity changed alternative time source) (quadrupoleCenter alternative time receiver) -
      vorticityComplexStrain (quadrupoleDensity changed reference time source) (quadrupoleCenter reference time receiver)‖ ≤ budget ∧
    ‖relativeBlockSourceShapeInput changed alternative reference receiver source time‖ ≤ budget := by
  obtain ⟨rawCap, rawPositive, blockConstant, blockNonnegative, factory⟩ := exists_uniform_actual_incoming_source_block_return
  obtain ⟨chartRadius, chartPositive, projection⟩ := exists_reference_strain_vector_projection_bound
  refine ⟨rawCap, rawPositive, 5 * blockConstant, by positivity, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  have sharpPositive : 0 < min chartRadius (1 / 4 : ℝ) := lt_min chartPositive (by norm_num)
  filter_upwards [factory scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative
      rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative sharpPositive,
    scales.eventually_cascade_quadrupole_foreign_clearance amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive (factorSmall.trans (by norm_num)),
    eventually_ge_atTop (1 : ℝ)] with frequency estimates sharp clearance frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source ordered nonterminal finish finishNonnegative finishBound
    radialSmall time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let alternative := prepared.trajectory.movingFamily.patchMotion
  let reference := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let gap := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
  let length := changed.length (source.val + 1)
  let state := prepared.rawSourceCenteredState time source +
    ‖relativeNormalizedFirstMoment changed alternative prepared.reference source time‖ +
    ‖quadrupoleCenter alternative time source - quadrupoleCenter reference time source‖ /
      changed.location (source.val + 1) + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
  let strength := changed.circulation (source.val + 1) * length ^ 2 / gap ^ 4 *
    (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1)) * state +
      changed.circulation (source.val + 1) * length ^ 2 / gap ^ 5 *
        ‖quadrupoleCenter alternative time receiver - quadrupoleCenter reference time receiver‖
  have fullInside : time ∈ Icc 0 path.stop := ⟨inside.1, inside.2.trans finishBound⟩
  have different : receiver ≠ source := fun same => by simp only [same, lt_self_iff_false] at ordered
  have member : source ∈ Finset.univ.erase receiver := Finset.mem_erase.mpr ⟨different.symm, Finset.mem_univ _⟩
  have distancePositive : 0 < gap / 8 := div_pos
    (changed.location_distance_pos (fun same => different (Fin.ext (Nat.add_right_cancel same)))) (by norm_num)
  have gaps := clearance count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time fullInside receiver
  have firstIdentity := incoming_coefficient_one_eq_literal_strain prepared.referenceWitness.trajectory.movingFamily changed
    prepared.referenceWitness.densityIdentity source (fun current => quadrupoleCenter reference current receiver) time
    distancePositive (gaps.1 source member)
  have secondIdentity := incoming_coefficient_one_eq_literal_strain prepared.trajectory.movingFamily changed
    prepared.densityIdentity source (fun current => quadrupoleCenter alternative current receiver) time
    distancePositive (gaps.2 source member)
  have sourceData := estimates count phase dipoleAngle prepared path receiver source ordered nonterminal finish finishNonnegative
    finishBound radialSmall time inside 0 (by norm_num)
    (div_nonneg (scales.location_pos _).le (by norm_num))
  dsimp only at sourceData
  have coefficientBound := (sourceData.1.le_tsum 0 (fun power _ => mul_nonneg (by positivity) (norm_nonneg _))).trans sourceData.2
  simp only [zero_add, pow_one] at coefficientBound
  rw [secondIdentity, firstIdentity] at coefficientBound
  change 96 * ‖vorticityComplexStrain (quadrupoleDensity changed alternative time source) (quadrupoleCenter alternative time receiver) -
    vorticityComplexStrain (quadrupoleDensity changed reference time source) (quadrupoleCenter reference time receiver)‖ ≤
      blockConstant * strength at coefficientBound
  have strainBound : ‖vorticityComplexStrain (quadrupoleDensity changed alternative time source) (quadrupoleCenter alternative time receiver) -
      vorticityComplexStrain (quadrupoleDensity changed reference time source) (quadrupoleCenter reference time receiver)‖ ≤
        blockConstant * strength := by
    have nonnegative := norm_nonneg (vorticityComplexStrain (quadrupoleDensity changed alternative time source) (quadrupoleCenter alternative time receiver) -
      vorticityComplexStrain (quadrupoleDensity changed reference time source) (quadrupoleCenter reference time receiver))
    linarith only [coefficientBound, nonnegative]
  have defect := sharp prepared.toCascadeMaterialPreparedPair time ⟨inside.1, fullInside.2.trans path.stopBound⟩ receiver
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
    (vorticityComplexStrain (quadrupoleDensity changed alternative time source) (quadrupoleCenter alternative time receiver) -
      vorticityComplexStrain (quadrupoleDensity changed reference time source) (quadrupoleCenter reference time receiver))
    positiveNonzero negativeNonzero chartSmall
  rw [prepared.referenceIdentity] at projected
  change ‖relativeBlockSourceShapeInput changed alternative reference receiver source time‖ ≤ _ at projected
  have vectorBound := projected.trans (mul_le_mul_of_nonneg_left strainBound (by norm_num : (0 : ℝ) ≤ 5))
  have strengthNonnegative : 0 ≤ strength := by
    have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
    have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
    have circulationNonnegative := (changed.circulation_pos frequencyPositive ratioPositive (source.val + 1)).le
    have sourcePositive := changed.location_pos (source.val + 1)
    have receiverPositive := changed.location_pos (receiver.val + 1)
    have lengthPositive := changed.length_pos (source.val + 1)
    dsimp only [strength, state, CascadeSourcePreparedPair.rawSourceCenteredState, CascadeSourcePreparedPair.rawSourceShapeBudget]
    positivity
  have enlarged : blockConstant * strength ≤ (5 * blockConstant) * strength := by
    nlinarith only [mul_nonneg blockNonnegative strengthNonnegative]
  rw [prepared.referenceIdentity]
  constructor
  · simpa only [strength, state, alternative, reference, gap, length, prepared.referenceIdentity] using strainBound.trans enlarged
  · simpa only [strength, state, alternative, reference, gap, length, prepared.referenceIdentity, mul_assoc] using vectorBound

end EulerNonuniqueness.Paper
