import EulerNonuniqueness.Section3.MovingStrainRealUniform
import EulerNonuniqueness.Section3.MovingStrainPhysicalPhaseDerivative
import EulerNonuniqueness.Section3.RelabeledForcingPrimitiveSeries
import EulerNonuniqueness.Section6.ExteriorLeadingCoefficientBound

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

def exteriorStrainModulatedCoefficient {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (frequency time : ℝ) : ℂ :=
  diskForcingPhase 0 frequency time * family.exteriorTaylorCoefficient (Finset.univ.erase index)
    (family.patch index).center (family.patch index).radius 1 time

def exteriorStrainPhysicalCorrection {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (angular : PeriodicC1HolderHalf) (frequency time : ℝ) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  frequency⁻¹ • movingStrainRealCorrectionCLM (diskRelabelCurve angular 1)
    (family.exteriorStrainModulatedCoefficient index frequency time)

def canonicalExteriorAffineCoordinate {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (angular : PeriodicC1HolderHalf) (frequency time : ℝ)
    (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  data - family.relabeledExteriorForcingPrimitive index angular frequency time -
    family.exteriorStrainPhysicalCorrection index angular frequency time (data - diskRelabelCurve angular 1)

theorem exteriorStrainPhysicalCorrection_eq_smul {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (angular : PeriodicC1HolderHalf) (frequency time : ℝ) :
    family.exteriorStrainPhysicalCorrection index angular frequency time =
      frequency⁻¹ • movingStrainRealCorrectionCLM (diskRelabelCurve angular 1)
        (family.exteriorStrainModulatedCoefficient index frequency time) := rfl

theorem canonicalExteriorAffineCoordinate_exists_uniform_near_identity_bound :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (angular : PeriodicC1HolderHalf), ‖angular‖ ≤ radius →
      (∀ label, star (angular.val.1 label) = angular.val.1 label) →
      ∀ {frequency time distance weight : ℝ}, frequency ≠ 0 → 0 < distance → 0 ≤ weight →
      4 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time)
        ((family.patch index).center time) position) ≤ weight →
      ∀ data : PeriodicC1HolderHalf,
      ‖family.canonicalExteriorAffineCoordinate index angular frequency time data - data‖ ≤
        constant * (weight / |frequency|) * (1 + ‖data - diskRelabelCurve angular 1‖) := by
  obtain ⟨correctionRadius, correctionPositive, correctionConstant, correctionOne, correctionBounds, _⟩ :=
    movingStrainRealCorrectionCLM_exists_uniform_relabel_bounds
  let constant := 64 / Real.pi + correctionConstant / (2 * Real.pi) + 1
  have constantOne : 1 ≤ constant := by
    have positive : 0 ≤ 64 / Real.pi + correctionConstant / (2 * Real.pi) := by positivity
    dsimp [constant]
    linarith
  refine ⟨min correctionRadius (1 / 4), lt_min correctionPositive (by norm_num), constant, constantOne, ?_⟩
  intro count family index angular inside realValues frequency time distance weight nonzero positive weightNonnegative
    small separated weightBound data
  have angularSmall : ‖angular‖ < 1 / 2 := (inside.trans (min_le_right _ _)).trans_lt (by norm_num)
  have primitiveBound := family.relabeledExteriorForcingPrimitive_norm_le index angular angularSmall realValues
    nonzero positive weightNonnegative small separated weightBound
  have coefficientBound : ‖family.exteriorStrainModulatedCoefficient index frequency time‖ ≤ weight / (2 * Real.pi) := by
    rw [exteriorStrainModulatedCoefficient, norm_mul, diskForcingPhase_norm, one_mul]
    exact family.exteriorTaylorCoefficient_one_norm_le index time distance weight positive separated weightBound
  have correctionBound : ‖family.exteriorStrainPhysicalCorrection index angular frequency time‖ ≤
      (correctionConstant / (2 * Real.pi)) * (weight / |frequency|) := by
    rw [exteriorStrainPhysicalCorrection, norm_smul, Real.norm_eq_abs, abs_inv]
    have actual := (correctionBounds angular (inside.trans (min_le_left _ _)) _).trans
      (mul_le_mul_of_nonneg_left coefficientBound (by linarith))
    exact (mul_le_mul_of_nonneg_left actual (by positivity)).trans_eq (by ring)
  have identity : family.canonicalExteriorAffineCoordinate index angular frequency time data - data =
      -family.relabeledExteriorForcingPrimitive index angular frequency time -
        family.exteriorStrainPhysicalCorrection index angular frequency time (data - diskRelabelCurve angular 1) := by
    unfold canonicalExteriorAffineCoordinate
    abel
  rw [identity]
  calc
    _ ≤ ‖family.relabeledExteriorForcingPrimitive index angular frequency time‖ +
        ‖family.exteriorStrainPhysicalCorrection index angular frequency time (data - diskRelabelCurve angular 1)‖ := by
      simpa only [norm_neg] using norm_sub_le (-family.relabeledExteriorForcingPrimitive index angular frequency time)
        (family.exteriorStrainPhysicalCorrection index angular frequency time (data - diskRelabelCurve angular 1))
    _ ≤ 64 * weight / (Real.pi * |frequency|) +
        ((correctionConstant / (2 * Real.pi)) * (weight / |frequency|)) * ‖data - diskRelabelCurve angular 1‖ :=
      add_le_add primitiveBound ((family.exteriorStrainPhysicalCorrection index angular frequency time).le_opNorm _ |>.trans
        (mul_le_mul_of_nonneg_right correctionBound (norm_nonneg _)))
    _ ≤ _ := by
      have leftover : 0 ≤ (weight / |frequency|) *
          (correctionConstant / (2 * Real.pi) + 1 +
            (64 / Real.pi + 1) * ‖data - diskRelabelCurve angular 1‖) := by positivity
      rw [show constant = 64 / Real.pi + correctionConstant / (2 * Real.pi) + 1 from rfl]
      apply sub_nonneg.mp
      convert leftover using 1 <;> ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
