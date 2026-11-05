import EulerNonuniqueness.Section3.CanonicalExteriorAffineCoordinate
import EulerNonuniqueness.Section3.CanonicalExteriorValueBound

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

theorem exteriorStrainPhysicalCorrection_exists_uniform_norm_bound :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (angular : PeriodicC1HolderHalf), ‖angular‖ ≤ radius →
      ∀ {frequency time distance weight : ℝ}, 0 < distance → 0 ≤ weight →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time)
        ((family.patch index).center time) position) ≤ weight →
      ‖family.exteriorStrainPhysicalCorrection index angular frequency time‖ ≤ constant * (weight / |frequency|) := by
  obtain ⟨radius, radiusPositive, correctionConstant, correctionOne, correctionBounds, _⟩ :=
    movingStrainRealCorrectionCLM_exists_uniform_relabel_bounds
  let constant := correctionConstant / (2 * Real.pi) + 1
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ correctionConstant / (2 * Real.pi) := by positivity
    dsimp [constant]
    linarith
  refine ⟨radius, radiusPositive, constant, constantOne, ?_⟩
  intro count family index angular inside frequency time distance weight positive weightNonnegative separated weightBound
  have coefficientBound : ‖family.exteriorStrainModulatedCoefficient index frequency time‖ ≤ weight / (2 * Real.pi) := by
    rw [exteriorStrainModulatedCoefficient, norm_mul, diskForcingPhase_norm, one_mul]
    exact family.exteriorTaylorCoefficient_one_norm_le index time distance weight positive separated weightBound
  rw [exteriorStrainPhysicalCorrection, norm_smul, Real.norm_eq_abs, abs_inv]
  have actual := (correctionBounds angular inside _).trans
    (mul_le_mul_of_nonneg_left coefficientBound (by linarith))
  have scaled := mul_le_mul_of_nonneg_left actual (show 0 ≤ |frequency|⁻¹ by positivity)
  have enlarge : correctionConstant / (2 * Real.pi) ≤ constant := by dsimp [constant]; linarith
  exact scaled.trans (by
    have numerical := mul_le_mul_of_nonneg_right enlarge (div_nonneg weightNonnegative (abs_nonneg frequency))
    convert numerical using 1 <;> ring)

theorem exteriorStrainPhysicalCorrection_canonicalField_exists_uniform_bound :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (time distance weight frequency : ℝ) (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
        (small : 48 * (family.patch index).radius ≤ distance)
        (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
          distance ≤ ‖(family.patch index).center time - position‖)
        (weightBound : (∫ position, inverseSquareVorticityWeight
          (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight)
        (phase : Circle) (angular increment : PeriodicC1HolderHalf), ‖angular‖ ≤ radius → ‖increment‖ ≤ radius →
      ‖family.exteriorStrainPhysicalCorrection index angular frequency time
        (family.canonicalProjectedExteriorContourField index time distance positive
          (by linarith [(family.patch index).radius_positive]) separated phase (standardCircleBanach + increment))‖ ≤
        constant * weight ^ 2 / |frequency| := by
  obtain ⟨correctionRadius, correctionPositive, correctionConstant, correctionOne, correctionBounds⟩ :=
    exteriorStrainPhysicalCorrection_exists_uniform_norm_bound
  obtain ⟨valueRadius, valuePositive, _, valueConstant, valueOne, valueBounds⟩ :=
    canonicalProjectedExteriorContourField_exists_uniform_value_bound
  let radius := min correctionRadius valueRadius
  let constant := correctionConstant * valueConstant + 1
  have constantOne : 1 ≤ constant := by dsimp [constant]; nlinarith
  refine ⟨radius, lt_min correctionPositive valuePositive, constant, constantOne, ?_⟩
  intro count family index time distance weight frequency positive weightNonnegative small separated weightBound
    phase angular increment angularSmall incrementSmall
  have correctionBound := correctionBounds family index angular (angularSmall.trans (min_le_left _ _))
    positive weightNonnegative separated weightBound (frequency := frequency) (time := time)
  have valueBound := valueBounds family index time distance weight positive weightNonnegative small separated weightBound phase increment
    (incrementSmall.trans (min_le_right _ _))
  have actual := (family.exteriorStrainPhysicalCorrection index angular frequency time).le_opNorm
    (family.canonicalProjectedExteriorContourField index time distance positive
      (by linarith [(family.patch index).radius_positive]) separated phase (standardCircleBanach + increment))
  have product := mul_le_mul correctionBound valueBound (norm_nonneg _) (by positivity : 0 ≤ correctionConstant * (weight / |frequency|))
  have enlarged : correctionConstant * valueConstant ≤ constant := by dsimp [constant]; linarith
  exact actual.trans (product.trans (by
    have numerical := mul_le_mul_of_nonneg_right enlarged (div_nonneg (sq_nonneg weight) (abs_nonneg frequency))
    convert numerical using 1 <;> ring))

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
