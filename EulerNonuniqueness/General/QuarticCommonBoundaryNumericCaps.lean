import EulerNonuniqueness.General.QuarticCanonicalMaterialMargins
import EulerNonuniqueness.General.QuarticConfinementBudget
import EulerNonuniqueness.General.QuarticMaterialBudget

namespace EulerNonuniqueness.General

set_option maxHeartbeats 2000000

theorem exists_uniform_quartic_common_boundary_numeric_caps
    {forcingConstant radiusCoefficient mapCoefficient shiftCoefficient quadraticConstant forcingRadius shapeRadius : ℝ}
    (forcingOne : 1 ≤ forcingConstant) (coefficientLarge : 600 * (forcingConstant + 1) ≤ radiusCoefficient)
    (mapNonnegative : 0 ≤ mapCoefficient) (shiftNonnegative : 0 ≤ shiftCoefficient)
    (quadraticOne : 1 ≤ quadraticConstant) (forcingPositive : 0 < forcingRadius) (shapePositive : 0 < shapeRadius) :
    ∃ rootMin ≥ (8 : ℝ), ∀ scaleRoot : ℝ, rootMin ≤ scaleRoot →
      ∀ frequency weight mass distance geometricRatio : ℝ, 1 ≤ frequency → 0 ≤ weight → 0 ≤ mass → 0 < distance →
      0 ≤ geometricRatio → weight ≤ forcingConstant * frequency →
      geometricRatio ≤ forcingConstant / (scaleRoot * frequency) →
      weight ^ 2 + mass * weight / distance ^ 2 ≤ forcingConstant * frequency ^ 2 →
      let strength := scaleRoot ^ 3 * frequency ^ 4
      let radius := radiusCoefficient / (scaleRoot ^ 2 * frequency ^ 2)
      0 < radius ∧ radius ≤ 1 ∧ radius ≤ shapeRadius ∧ weight / strength ≤ forcingRadius ∧
      weight / strength ≤ radius ∧ (weight / strength) ^ 2 ≤ radius ^ 3 ∧
      (weight / strength) * geometricRatio ≤ radius ^ 2 ∧
      (12 * (46 * weight ^ 2 / Real.pi ^ 2 + 6 * mass * weight / (Real.pi ^ 2 * distance ^ 2))) / strength ≤ strength * radius ^ 3 ∧
      mapCoefficient * (weight / strength) ≤ radius / 2 ∧
      shiftCoefficient * (weight / strength) ≤ radius / 8 ∧ quadraticConstant * radius ≤ 1 / 2 ∧
      strength * radius ^ 2 ≤ 1 := by
  have forcingNonnegative : 0 ≤ forcingConstant := by linarith
  have quadraticPositive : 0 < quadraticConstant := by linarith
  have coefficientOne : 1 ≤ radiusCoefficient := by linarith
  have coefficientPositive : 0 < radiusCoefficient := by linarith
  have coefficientForcing : forcingConstant ≤ radiusCoefficient - 1 := by linarith
  let tolerance := min shapeRadius (min forcingRadius (1 / (2 * quadraticConstant)))
  have tolerancePositive : 0 < tolerance := by dsimp only [tolerance]; positivity
  obtain ⟨shapeRoot, shapeEight, shapes⟩ := exists_uniform_quartic_shape_confinement_root
    (forcingConstant := radiusCoefficient - 1) (neutralConstant := 0) (shapeConstant := 1) (terminal := 0)
    (by linarith) (by norm_num) (by norm_num) (by norm_num) tolerancePositive
  let rootMin := max shapeRoot (max (8 * forcingConstant * (mapCoefficient + shiftCoefficient + 1)) (radiusCoefficient ^ 2 + 1))
  refine ⟨rootMin, shapeEight.trans (le_max_left _ _), ?_⟩
  intro scaleRoot rootLarge frequency weight mass distance geometricRatio frequencyOne weightNonnegative massNonnegative distancePositive
    ratioNonnegative weightBound ratioBound numeratorBound
  have rootEight : 8 ≤ scaleRoot := shapeEight.trans ((le_max_left _ _).trans rootLarge)
  have rootPositive : 0 < scaleRoot := by linarith
  have frequencyPositive : 0 < frequency := by linarith
  have enlargedWeight := weightBound.trans (mul_le_mul_of_nonneg_right coefficientForcing frequencyPositive.le)
  have shape := shapes scaleRoot ((le_max_left _ _).trans rootLarge) frequency weight frequencyOne weightNonnegative enlargedWeight
  simp only [sub_add_cancel, zero_mul, zero_add, mul_zero, one_mul] at shape
  have margins := quartic_canonical_material_margins forcingOne rootEight frequencyOne weightNonnegative massNonnegative
    distancePositive ratioNonnegative weightBound ratioBound numeratorBound
  dsimp only at margins
  have radiusOrder := div_le_div_of_nonneg_right coefficientLarge
    (by positivity : 0 ≤ scaleRoot ^ 2 * frequency ^ 2)
  have squareOrder := pow_le_pow_left₀ margins.1.le radiusOrder 2
  have cubeOrder := pow_le_pow_left₀ margins.1.le radiusOrder 3
  have numeratorWeight : weight ≤ forcingConstant * frequency ^ 2 := by
    have frequencySquare : frequency ≤ frequency ^ 2 := by nlinarith
    exact weightBound.trans (mul_le_mul_of_nonneg_left frequencySquare forcingNonnegative)
  have epsilonRelative := quartic_frequency_numerator_ratio forcingNonnegative rootPositive frequencyPositive numeratorWeight
  have smallRadiusOrder := div_le_div_of_nonneg_right
    (show forcingConstant + 1 ≤ radiusCoefficient by linarith) (by positivity : 0 ≤ scaleRoot ^ 2 * frequency ^ 2)
  have epsilonRadius := epsilonRelative.trans (mul_le_mul_of_nonneg_left smallRadiusOrder (div_nonneg forcingNonnegative rootPositive.le))
  have mapRoot : 8 * forcingConstant * (mapCoefficient + shiftCoefficient + 1) ≤ scaleRoot :=
    (le_max_left _ _).trans ((le_max_right _ _).trans rootLarge)
  have mapFraction : mapCoefficient * (forcingConstant / scaleRoot) ≤ 1 / 8 := by
    have numerator : mapCoefficient * forcingConstant ≤ (1 / 8) * scaleRoot := by
      nlinarith [mul_nonneg forcingNonnegative shiftNonnegative]
    convert (div_le_iff₀ rootPositive).mpr numerator using 1 <;> ring
  have shiftFraction : shiftCoefficient * (forcingConstant / scaleRoot) ≤ 1 / 8 := by
    have numerator : shiftCoefficient * forcingConstant ≤ (1 / 8) * scaleRoot := by
      nlinarith [mul_nonneg forcingNonnegative mapNonnegative]
    convert (div_le_iff₀ rootPositive).mpr numerator using 1 <;> ring
  have mapBound : mapCoefficient * (weight / (scaleRoot ^ 3 * frequency ^ 4)) ≤
      (radiusCoefficient / (scaleRoot ^ 2 * frequency ^ 2)) / 8 := by
    calc
      _ ≤ mapCoefficient * (forcingConstant / scaleRoot * (radiusCoefficient / (scaleRoot ^ 2 * frequency ^ 2))) :=
        mul_le_mul_of_nonneg_left epsilonRadius mapNonnegative
      _ = (mapCoefficient * (forcingConstant / scaleRoot)) * (radiusCoefficient / (scaleRoot ^ 2 * frequency ^ 2)) := by ring
      _ ≤ (1 / 8) * (radiusCoefficient / (scaleRoot ^ 2 * frequency ^ 2)) := mul_le_mul_of_nonneg_right mapFraction shape.1.le
      _ = _ := by ring
  have shiftBound : shiftCoefficient * (weight / (scaleRoot ^ 3 * frequency ^ 4)) ≤
      (radiusCoefficient / (scaleRoot ^ 2 * frequency ^ 2)) / 8 := by
    calc
      _ ≤ shiftCoefficient * (forcingConstant / scaleRoot * (radiusCoefficient / (scaleRoot ^ 2 * frequency ^ 2))) :=
        mul_le_mul_of_nonneg_left epsilonRadius shiftNonnegative
      _ = (shiftCoefficient * (forcingConstant / scaleRoot)) * (radiusCoefficient / (scaleRoot ^ 2 * frequency ^ 2)) := by ring
      _ ≤ (1 / 8) * (radiusCoefficient / (scaleRoot ^ 2 * frequency ^ 2)) := mul_le_mul_of_nonneg_right shiftFraction shape.1.le
      _ = _ := by ring
  have quadraticSmall := shape.2.2.2.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have quadraticBound := (le_div_iff₀ (by positivity : 0 < 2 * quadraticConstant)).mp quadraticSmall
  have strengthIdentity := quartic_frequency_cubic_ratio (radiusCoefficient := radiusCoefficient) rootPositive.ne' frequencyPositive.ne'
  have strengthSmall : scaleRoot ^ 3 * frequency ^ 4 * (radiusCoefficient / (scaleRoot ^ 2 * frequency ^ 2)) ^ 2 ≤ 1 := by
    rw [strengthIdentity]
    apply (div_le_one₀ rootPositive).mpr
    have large : radiusCoefficient ^ 2 + 1 ≤ scaleRoot := (le_max_right _ _).trans ((le_max_right _ _).trans rootLarge)
    linarith
  refine ⟨shape.1, shape.2.1, shape.2.2.2.le.trans (min_le_left _ _), ?_, ?_, margins.2.2.1.trans cubeOrder,
    margins.2.2.2.1.trans squareOrder,
    margins.2.2.2.2.trans (mul_le_mul_of_nonneg_left cubeOrder (by positivity)), ?_, shiftBound, ?_, strengthSmall⟩
  · exact (shape.2.2.1.trans (by linarith [shape.1])).trans
      (shape.2.2.2.le.trans ((min_le_right _ _).trans (min_le_left _ _)))
  · linarith [shape.2.2.1, shape.1]
  · linarith [mapBound, shape.1]
  · linarith [quadraticBound]

end EulerNonuniqueness.General
