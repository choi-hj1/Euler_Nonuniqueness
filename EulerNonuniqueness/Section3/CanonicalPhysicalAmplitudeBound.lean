import EulerNonuniqueness.Section3.CanonicalExteriorAffineCoordinate
import EulerNonuniqueness.Section6.MovingCoefficientStrongerWeights

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

def exteriorStrainAmplitudeCorrection {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (angular : PeriodicC1HolderHalf) (frequency time : ℝ) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  frequency⁻¹ • movingStrainRealCorrectionCLM (diskRelabelCurve angular 1)
    (diskForcingPhase 0 frequency time * family.exteriorMaterialCoefficientDerivative index 0 time)

theorem exteriorStrainAmplitudeCorrection_exists_uniform_norm_bound :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (angular : PeriodicC1HolderHalf), ‖angular‖ ≤ radius →
      ∀ {frequency time distance weight mass : ℝ},
      time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime →
      (∀ label, (family.patch index).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch index).boundary time label)) →
      (family.patch index).center =ᶠ[nhds time] (family.patch index).centroid →
      0 < distance → 0 ≤ weight → 0 ≤ mass → 8 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time)
        ((family.patch index).center time) position) ≤ weight →
      (∫ position, |family.patchVorticity time index position|) ≤ mass →
      ‖family.exteriorStrainAmplitudeCorrection index angular frequency time‖ ≤
        constant * (weight ^ 2 + mass * weight / distance ^ 2) / |frequency| := by
  obtain ⟨radius, positiveRadius, correctionConstant, correctionOne, correctionBounds, _⟩ :=
    movingStrainRealCorrectionCLM_exists_uniform_relabel_bounds
  let constant := 52 * correctionConstant / Real.pi ^ 2 + 1
  have correctionNonnegative : 0 ≤ correctionConstant := by linarith
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ 52 * correctionConstant / Real.pi ^ 2 := by positivity
    dsimp [constant]
    linarith
  refine ⟨radius, positiveRadius, constant, constantOne, ?_⟩
  intro count family index angular angularSmall frequency time distance weight mass inside material centered
    positive weightNonnegative massNonnegative small separated weightBound massBound
  have actualSums := family.exteriorMaterialCoefficientDerivative_stronger_weight_bounds index inside material centered
    positive weightNonnegative massNonnegative (factor := 1) (by norm_num)
    (by simpa only [one_mul] using small) separated weightBound massBound
  have single := actualSums.1.le_tsum 0 (fun _ _ => by positivity)
  norm_num only [mul_one, one_mul, zero_add, pow_one] at single actualSums
  have amplitudeBound : ‖family.exteriorMaterialCoefficientDerivative index 0 time‖ ≤
      46 * weight ^ 2 / Real.pi ^ 2 + 6 * mass * weight / (Real.pi ^ 2 * distance ^ 2) := by
    have doubled := single.trans actualSums.2
    linarith [norm_nonneg (family.exteriorMaterialCoefficientDerivative index 0 time)]
  have phaseBound : ‖diskForcingPhase 0 frequency time * family.exteriorMaterialCoefficientDerivative index 0 time‖ ≤
      46 * weight ^ 2 / Real.pi ^ 2 + 6 * mass * weight / (Real.pi ^ 2 * distance ^ 2) := by
    simpa only [norm_mul, diskForcingPhase_norm, one_mul] using amplitudeBound
  have correctionBound := (correctionBounds angular angularSmall _).trans
    (mul_le_mul_of_nonneg_left phaseBound correctionNonnegative)
  have scaleNonnegative : 0 ≤ weight ^ 2 + mass * weight / distance ^ 2 := by positivity
  have amplitudeScale : correctionConstant *
      (46 * weight ^ 2 / Real.pi ^ 2 + 6 * mass * weight / (Real.pi ^ 2 * distance ^ 2)) ≤
      constant * (weight ^ 2 + mass * weight / distance ^ 2) := by
    have enlarged : 52 * correctionConstant / Real.pi ^ 2 ≤ constant := by dsimp [constant]; linarith
    have first : 46 * correctionConstant / Real.pi ^ 2 ≤ constant :=
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num : (46 : ℝ) ≤ 52) correctionNonnegative) (sq_nonneg Real.pi)).trans enlarged
    have second : 6 * correctionConstant / Real.pi ^ 2 ≤ constant :=
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num : (6 : ℝ) ≤ 52) correctionNonnegative) (sq_nonneg Real.pi)).trans enlarged
    have numerical := add_le_add (mul_le_mul_of_nonneg_right first (sq_nonneg weight))
      (mul_le_mul_of_nonneg_right second (div_nonneg (mul_nonneg massNonnegative weightNonnegative) (sq_nonneg distance)))
    convert numerical using 1 <;> ring
  rw [exteriorStrainAmplitudeCorrection, norm_smul, Real.norm_eq_abs, abs_inv]
  exact (mul_le_mul_of_nonneg_left (correctionBound.trans amplitudeScale) (show 0 ≤ |frequency|⁻¹ by positivity)).trans_eq (by ring)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
