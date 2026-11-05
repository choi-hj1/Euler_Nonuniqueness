import EulerNonuniqueness.Section3.MovingStrainAffineUniform
import EulerNonuniqueness.Section6.ExteriorLeadingCoefficientBound

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace

open EulerNonuniqueness.Section6

theorem canonicalLeadingStrainAffineResidual_exists_uniform_bound :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count) (time distance weight : ℝ),
      0 < distance → 0 ≤ weight →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight (family.subfamilyVorticity (Finset.univ.erase index) time)
        ((family.patch index).center time) position) ≤ weight →
      ∀ (phase : Circle) (angular : PeriodicC1HolderHalf),
      ‖angular‖ ≤ radius → angular ∈ contourContinuousVectorSubmodule →
      (∀ label, star (angular.val.1 label) = angular.val.1 label) →
      ∀ direction : PeriodicC1HolderHalf,
      ‖diskRelabelCurve angular 1 - standardCircleBanach‖ + ‖direction‖ ≤ radius →
      direction ∈ contourContinuousVectorSubmodule →
      contourCentroidFunctional (diskRelabelCurve angular 1 + direction) = contourCentroidFunctional (diskRelabelCurve angular 1) →
      ‖movingStrainAffineResidual (diskRelabelCurve angular 1)
        ((phase : ℂ)⁻¹ ^ 2 * family.exteriorTaylorCoefficient (Finset.univ.erase index)
          (family.patch index).center (family.patch index).radius 1 time)
        (diskRelabelCurve angular 1 + direction)‖ ≤ constant * weight * ‖direction‖ ^ 2 := by
  obtain ⟨radius, positiveRadius, strainConstant, strainOne, bound⟩ :=
    movingStrainAffineResidual_exists_uniform_quadratic_bound
  let constant := strainConstant / (2 * Real.pi) + 1
  have strainNonnegative : 0 ≤ strainConstant := by linarith
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ strainConstant / (2 * Real.pi) := by positivity
    dsimp [constant]
    linarith
  refine ⟨radius, positiveRadius, constant, constantOne, ?_⟩
  intro count family index time distance weight positive weightNonnegative separated weightBound phase angular
    angularSmall angularMember realValues direction inside member centered
  have coefficient := family.exteriorTaylorCoefficient_rotated_one_norm_le index time distance weight
    positive separated weightBound phase
  have actual := bound angular angularSmall angularMember realValues
    ((phase : ℂ)⁻¹ ^ 2 * family.exteriorTaylorCoefficient (Finset.univ.erase index)
      (family.patch index).center (family.patch index).radius 1 time) direction inside member centered
  calc
    _ ≤ strainConstant * (weight / (2 * Real.pi)) * ‖direction‖ ^ 2 := by
      exact actual.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left coefficient strainNonnegative) (sq_nonneg ‖direction‖))
    _ ≤ constant * weight * ‖direction‖ ^ 2 := by
      have scale : strainConstant / (2 * Real.pi) ≤ constant := by dsimp [constant]; linarith
      have scaled := mul_le_mul_of_nonneg_right scale (mul_nonneg weightNonnegative (sq_nonneg ‖direction‖))
      convert scaled using 1 <;> ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
