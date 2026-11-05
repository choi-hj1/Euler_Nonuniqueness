import EulerNonuniqueness.Section3.RelabeledExteriorHigherPrimitive
import EulerNonuniqueness.Section3.DiskRotatingUniformDifference

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] rotatingSecondFrechetC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

theorem relabeledExteriorHigherForcingPrimitive_exists_uniform_self_difference_bound :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (angular direction : PeriodicC1HolderHalf), ‖angular‖ ≤ radius →
      (∀ label, star (angular.val.1 label) = angular.val.1 label) →
      ∀ {frequency time distance weight : ℝ}, frequency ≠ 0 → 0 < distance → 0 ≤ weight →
      4 * (family.patch index).radius ≤ distance →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) time)
        ((family.patch index).center time) position) ≤ weight →
      ‖diskRelabelCurve angular 1 - standardCircleBanach‖ + ‖direction‖ ≤ radius →
      ‖frequency • ((fderiv ℝ diskEulerRotatingField (diskRelabelCurve angular 1 + direction) -
          fderiv ℝ diskEulerRotatingField (diskRelabelCurve angular 1))
        (family.relabeledExteriorHigherForcingPrimitive index angular frequency time))‖ ≤
        constant * weight * ((family.patch index).radius / distance) * ‖direction‖ := by
  obtain ⟨derivativeRadius, derivativePositive, _, derivativeConstant, derivativeOne, derivativeBounds⟩ :=
    diskEulerRotatingField_exists_uniform_derivative_difference
  let radius := min derivativeRadius (1 / 4)
  let constant := 256 * derivativeConstant / Real.pi + 1
  have derivativeNonnegative : 0 ≤ derivativeConstant := by linarith
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ 256 * derivativeConstant / Real.pi := by positivity
    dsimp [constant]
    linarith
  refine ⟨radius, lt_min derivativePositive (by norm_num), constant, constantOne, ?_⟩
  intro count family index angular direction angularSmall realValues frequency time distance weight
    nonzero positive weightNonnegative small separated weightBound inside
  have angularHalf : ‖angular‖ < 1 / 2 := (angularSmall.trans (min_le_right _ _)).trans_lt (by norm_num)
  have derivativeBound := derivativeBounds (diskRelabelCurve angular 1) direction (inside.trans (min_le_left _ _))
  have tailBound := family.relabeledExteriorHigherForcingPrimitive_norm_bound index angular angularHalf realValues
    nonzero positive weightNonnegative small separated weightBound
  generalize operatorEq : fderiv ℝ diskEulerRotatingField (diskRelabelCurve angular 1 + direction) -
    fderiv ℝ diskEulerRotatingField (diskRelabelCurve angular 1) = operator at *
  generalize tailEq : family.relabeledExteriorHigherForcingPrimitive index angular frequency time = tail at *
  rw [norm_smul, Real.norm_eq_abs]
  have applied := (operator.le_opNorm tail).trans
    (mul_le_mul derivativeBound tailBound (norm_nonneg _) (by positivity : 0 ≤ derivativeConstant * ‖direction‖))
  have scaled := mul_le_mul_of_nonneg_left applied (abs_nonneg frequency)
  have frequencyPositive : 0 < |frequency| := abs_pos.mpr nonzero
  have identity : |frequency| * ((derivativeConstant * ‖direction‖) *
      (256 * (family.patch index).radius * weight / (Real.pi * |frequency| * distance))) =
      (256 * derivativeConstant / Real.pi) * weight * ((family.patch index).radius / distance) * ‖direction‖ := by
    field_simp [frequencyPositive.ne', positive.ne', Real.pi_ne_zero]
    <;> ring
  have coefficientLe : 256 * derivativeConstant / Real.pi ≤ constant := by dsimp [constant]; linarith
  exact scaled.trans (by
    rw [identity]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right coefficientLe weightNonnegative)
        (div_nonneg (family.patch index).radius_positive.le positive.le)) (norm_nonneg _))

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
