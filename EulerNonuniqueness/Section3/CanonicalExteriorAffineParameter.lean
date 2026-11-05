import EulerNonuniqueness.Section3.CanonicalExteriorAffineCoordinate
import EulerNonuniqueness.Section3.RelabeledExteriorPrimitiveUniformLipschitz
import EulerNonuniqueness.General.AffineParameterCoordinate

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

theorem canonicalExteriorAffineCoordinate_exists_uniform_parameter_lipschitz :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (first second : PeriodicC1HolderHalf), ‖first‖ ≤ radius → ‖second‖ ≤ radius →
      (∀ label, star (first.val.1 label) = first.val.1 label) →
      (∀ label, star (second.val.1 label) = second.val.1 label) →
      ∀ {frequency time distance weight : ℝ}, frequency ≠ 0 → 0 < distance → 0 ≤ weight →
      48 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time)
        ((family.patch index).center time) position) ≤ weight →
      ∀ data : PeriodicC1HolderHalf,
      ‖family.canonicalExteriorAffineCoordinate index first frequency time data -
        family.canonicalExteriorAffineCoordinate index second frequency time data‖ ≤
        constant * (weight / |frequency|) * (1 + ‖data - diskRelabelCurve second 1‖) * ‖first - second‖ := by
  obtain ⟨correctionRadius, correctionPositive, correctionConstant, correctionOne, correctionBounds, correctionDifference⟩ :=
    movingStrainRealCorrectionCLM_exists_uniform_relabel_bounds
  obtain ⟨primitiveRadius, primitivePositive, primitiveConstant, primitiveDifference⟩ :=
    relabeledExteriorForcingPrimitive_exists_uniform_parameter_lipschitz
  obtain ⟨baseRadius, basePositive, baseConstant, _, baseDifference⟩ := diskRelabelMap_exists_uniform_lipschitz
  let radius := min correctionRadius (min primitiveRadius baseRadius)
  let bound := 48 * (primitiveConstant : ℝ) / Real.pi + correctionConstant / (2 * Real.pi) + baseConstant + 1
  let constant := bound * (2 + bound) + 1
  have correctionNonnegative : 0 ≤ correctionConstant := by linarith
  have primitiveNonnegative : 0 ≤ 48 * (primitiveConstant : ℝ) / Real.pi := by positivity
  have correctionScaleNonnegative : 0 ≤ correctionConstant / (2 * Real.pi) := by positivity
  have boundNonnegative : 0 ≤ bound := by dsimp [bound]; positivity
  have primitiveLe : 48 * (primitiveConstant : ℝ) / Real.pi ≤ bound := by dsimp [bound]; linarith [baseConstant.coe_nonneg]
  have correctionLe : correctionConstant / (2 * Real.pi) ≤ bound := by dsimp [bound]; linarith [baseConstant.coe_nonneg]
  have baseLe : (baseConstant : ℝ) ≤ bound := by dsimp [bound]; linarith
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ bound * (2 + bound) := by positivity
    dsimp [constant]
    linarith
  have constantLe : bound * (2 + bound) ≤ constant := by dsimp [constant]; linarith
  refine ⟨radius, by dsimp [radius]; positivity, constant, constantOne, ?_⟩
  intro count family index first second firstNear secondNear firstReal secondReal
    frequency time distance weight nonzero positive weightNonnegative small separated weightBound data
  have firstCorrection := firstNear.trans (min_le_left _ _)
  have secondCorrection := secondNear.trans (min_le_left _ _)
  have firstPrimitive := firstNear.trans ((min_le_right _ _).trans (min_le_left _ _))
  have secondPrimitive := secondNear.trans ((min_le_right _ _).trans (min_le_left _ _))
  have firstBase := firstNear.trans ((min_le_right _ _).trans (min_le_right _ _))
  have secondBase := secondNear.trans ((min_le_right _ _).trans (min_le_right _ _))
  have epsilonNonnegative : 0 ≤ weight / |frequency| := by positivity
  have coefficientBound : ‖family.exteriorStrainModulatedCoefficient index frequency time‖ ≤ weight / (2 * Real.pi) := by
    rw [exteriorStrainModulatedCoefficient, norm_mul, diskForcingPhase_norm, one_mul]
    exact family.exteriorTaylorCoefficient_one_norm_le index time distance weight positive separated weightBound
  have primitiveEstimate : ‖family.relabeledExteriorForcingPrimitive index first frequency time -
      family.relabeledExteriorForcingPrimitive index second frequency time‖ ≤
      bound * (weight / |frequency|) * ‖first - second‖ := by
    have actual := primitiveDifference family index first second firstPrimitive secondPrimitive firstReal secondReal
      nonzero positive weightNonnegative small separated weightBound
    have numerical := mul_le_mul_of_nonneg_right primitiveLe
      (mul_nonneg epsilonNonnegative (norm_nonneg (first - second)))
    exact actual.trans (by convert numerical using 1 <;> ring)
  have correctionEstimate : ‖family.exteriorStrainPhysicalCorrection index first frequency time‖ ≤ bound * (weight / |frequency|) := by
    rw [exteriorStrainPhysicalCorrection, norm_smul, Real.norm_eq_abs, abs_inv]
    have actual := (correctionBounds first firstCorrection _).trans
      (mul_le_mul_of_nonneg_left coefficientBound correctionNonnegative)
    have scaled := mul_le_mul_of_nonneg_left actual (show 0 ≤ |frequency|⁻¹ by positivity)
    have numerical := mul_le_mul_of_nonneg_right correctionLe epsilonNonnegative
    exact scaled.trans (by convert numerical using 1 <;> ring)
  have correctionDifferenceEstimate :
      ‖family.exteriorStrainPhysicalCorrection index first frequency time -
        family.exteriorStrainPhysicalCorrection index second frequency time‖ ≤
      bound * (weight / |frequency|) * ‖first - second‖ := by
    rw [exteriorStrainPhysicalCorrection, exteriorStrainPhysicalCorrection, ← smul_sub,
      norm_smul, Real.norm_eq_abs, abs_inv]
    have actual := (correctionDifference first second firstCorrection secondCorrection _).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left coefficientBound correctionNonnegative) (norm_nonneg _))
    have scaled := mul_le_mul_of_nonneg_left actual (show 0 ≤ |frequency|⁻¹ by positivity)
    have numerical := mul_le_mul_of_nonneg_right correctionLe (mul_nonneg epsilonNonnegative (norm_nonneg (first - second)))
    exact scaled.trans (by convert numerical using 1 <;> ring)
  have baseEstimate := (baseDifference first second firstBase secondBase).trans
    (mul_le_mul_of_nonneg_right baseLe (norm_nonneg _))
  unfold canonicalExteriorAffineCoordinate
  generalize firstBaseEq : diskRelabelCurve first 1 = firstShape at *
  generalize secondBaseEq : diskRelabelCurve second 1 = secondShape at *
  generalize firstPrimitiveEq : family.relabeledExteriorForcingPrimitive index first frequency time = firstValue at *
  generalize secondPrimitiveEq : family.relabeledExteriorForcingPrimitive index second frequency time = secondValue at *
  generalize firstOperatorEq : family.exteriorStrainPhysicalCorrection index first frequency time = firstOperator at *
  generalize secondOperatorEq : family.exteriorStrainPhysicalCorrection index second frequency time = secondOperator at *
  have actual := EulerNonuniqueness.General.norm_affine_parameter_coordinate_difference_le data
    firstShape secondShape firstValue secondValue firstOperator secondOperator
    boundNonnegative epsilonNonnegative (norm_nonneg (first - second)) primitiveEstimate
    correctionDifferenceEstimate correctionEstimate baseEstimate
  exact actual.trans (by gcongr)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
