import EulerNonuniqueness.Section3.CanonicalExteriorAffineParameter

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

theorem canonicalExteriorAffineCoordinate_exists_common_shift_relative :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (firstAngular finalAngular : PeriodicC1HolderHalf), ‖firstAngular‖ ≤ radius → ‖finalAngular‖ ≤ radius →
      (∀ label, star (firstAngular.val.1 label) = firstAngular.val.1 label) →
      (∀ label, star (finalAngular.val.1 label) = finalAngular.val.1 label) →
      ∀ {frequency time distance weight : ℝ}, frequency ≠ 0 → 0 < distance → 0 ≤ weight →
      48 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight →
      ∀ firstData finalData : PeriodicC1HolderHalf,
      ‖(firstData - family.canonicalExteriorAffineCoordinate index firstAngular frequency time firstData) -
        (finalData - family.canonicalExteriorAffineCoordinate index finalAngular frequency time finalData)‖ ≤
      constant * (weight / |frequency|) *
        (‖firstData - finalData‖ + (1 + ‖finalData - diskRelabelCurve finalAngular 1‖) * ‖firstAngular - finalAngular‖) := by
  obtain ⟨parameterRadius, parameterPositive, parameterConstant, parameterOne, parameterBound⟩ :=
    canonicalExteriorAffineCoordinate_exists_uniform_parameter_lipschitz
  obtain ⟨correctionRadius, correctionPositive, correctionConstant, correctionOne, correctionBound, _⟩ :=
    movingStrainRealCorrectionCLM_exists_uniform_relabel_bounds
  let constant := parameterConstant + correctionConstant / (2 * Real.pi) + 1
  have correctionNonnegative : 0 ≤ correctionConstant / (2 * Real.pi) := by positivity
  have constantOne : 1 ≤ constant := by dsimp [constant]; linarith
  have parameterLe : parameterConstant ≤ constant := by dsimp [constant]; linarith
  have correctionLe : correctionConstant / (2 * Real.pi) ≤ constant := by dsimp [constant]; linarith
  refine ⟨min parameterRadius correctionRadius, lt_min parameterPositive correctionPositive,
    constant, constantOne, ?_⟩
  intro count family index firstAngular finalAngular firstInside finalInside firstReal finalReal
    frequency time distance weight nonzero positive weightNonnegative small separated weightBound firstData finalData
  have parameters := parameterBound family index firstAngular finalAngular
    (firstInside.trans (min_le_left _ _)) (finalInside.trans (min_le_left _ _)) firstReal finalReal
    nonzero positive weightNonnegative small separated weightBound finalData
  have coefficientBound : ‖family.exteriorStrainModulatedCoefficient index frequency time‖ ≤ weight / (2 * Real.pi) := by
    rw [exteriorStrainModulatedCoefficient, norm_mul, diskForcingPhase_norm, one_mul]
    exact family.exteriorTaylorCoefficient_one_norm_le index time distance weight positive separated weightBound
  have correctionNorm : ‖family.exteriorStrainPhysicalCorrection index firstAngular frequency time‖ ≤
      (correctionConstant / (2 * Real.pi)) * (weight / |frequency|) := by
    rw [exteriorStrainPhysicalCorrection, norm_smul, Real.norm_eq_abs, abs_inv]
    have raw := (correctionBound firstAngular (firstInside.trans (min_le_right _ _)) _).trans
      (mul_le_mul_of_nonneg_left coefficientBound (by linarith))
    exact (mul_le_mul_of_nonneg_left raw (by positivity)).trans_eq (by ring)
  have identity :
      (firstData - family.canonicalExteriorAffineCoordinate index firstAngular frequency time firstData) -
        (finalData - family.canonicalExteriorAffineCoordinate index finalAngular frequency time finalData) =
      family.exteriorStrainPhysicalCorrection index firstAngular frequency time (firstData - finalData) +
      (family.canonicalExteriorAffineCoordinate index finalAngular frequency time finalData -
        family.canonicalExteriorAffineCoordinate index firstAngular frequency time finalData) := by
    unfold canonicalExteriorAffineCoordinate
    simp only [map_sub]
    abel
  rw [identity]
  have applied := (family.exteriorStrainPhysicalCorrection index firstAngular frequency time).le_opNorm (firstData - finalData)
  rw [norm_sub_rev] at parameters
  have bound := add_le_add (applied.trans (mul_le_mul_of_nonneg_right correctionNorm (norm_nonneg _)))
    parameters
  apply (norm_add_le _ _).trans
  apply bound.trans
  have initial := mul_le_mul_of_nonneg_right correctionLe
    (mul_nonneg (by positivity : 0 ≤ weight / |frequency|) (norm_nonneg (firstData - finalData)))
  have final := mul_le_mul_of_nonneg_right parameterLe
    (mul_nonneg (mul_nonneg (by positivity : 0 ≤ weight / |frequency|)
      (by positivity : 0 ≤ 1 + ‖finalData - diskRelabelCurve finalAngular 1‖)) (norm_nonneg (firstAngular - finalAngular)))
  convert add_le_add initial final using 1 <;> ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
