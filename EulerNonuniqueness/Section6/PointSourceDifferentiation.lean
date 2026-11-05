import EulerNonuniqueness.Section6.PairedPhysicalStrain

noncomputable section

namespace EulerNonuniqueness.Section6

theorem fourPointExternalPointVelocity_hasFDerivAt (coefficient : ℝ) (positions : FourPointConfiguration)
    {location : ℂ} (noncollision : ∀ target, location - positions target ≠ 0) :
    HasFDerivAt (fourPointExternalPointVelocity coefficient positions)
      (fourPointExternalPointStrain coefficient positions location •
        (Complex.conjCLE : ℂ →L[ℝ] ℂ)) location := by
  have conjugate : HasFDerivAt (fun current : ℂ => star current)
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) location := Complex.conjCLE.hasFDerivAt
  have derivative := (fourPointExternalPointStrain_hasDerivAt coefficient positions noncollision).comp_hasFDerivAt location conjugate
  convert derivative using 1
  funext current
  simp only [fourPointExternalPointVelocity, fourPointCauchyField_conjugate, Function.comp_apply]

theorem fourPointExternalPointVelocity_fderiv_apply (coefficient : ℝ) (positions : FourPointConfiguration)
    {location : ℂ} (noncollision : ∀ target, location - positions target ≠ 0) (increment : ℂ) :
    fderiv ℝ (fourPointExternalPointVelocity coefficient positions) location increment =
      fourPointExternalPointStrain coefficient positions location * star increment := by
  rw [(fourPointExternalPointVelocity_hasFDerivAt coefficient positions noncollision).fderiv]
  simp only [ContinuousLinearMap.smul_apply, Complex.conjCLE_apply, smul_eq_mul, Complex.star_def]
  rfl

theorem fourPointExternalPointVelocity_fderiv_norm (coefficient : ℝ) (positions : FourPointConfiguration)
    {location : ℂ} (noncollision : ∀ target, location - positions target ≠ 0) :
    ‖fderiv ℝ (fourPointExternalPointVelocity coefficient positions) location‖ =
      ‖fourPointExternalPointStrain coefficient positions location‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro increment
    rw [fourPointExternalPointVelocity_fderiv_apply coefficient positions noncollision, norm_mul, norm_star]
  · have estimate := (fderiv ℝ (fourPointExternalPointVelocity coefficient positions) location).le_opNorm (1 : ℂ)
    simpa only [fourPointExternalPointVelocity_fderiv_apply coefficient positions noncollision, star_one, mul_one, norm_one] using estimate

theorem fourPointExternalPointVelocity_contDiffAt (coefficient : ℝ) (positions : FourPointConfiguration)
    {location : ℂ} (noncollision : ∀ target, location - positions target ≠ 0) :
    ContDiffAt ℝ 2 (fourPointExternalPointVelocity coefficient positions) location := by
  have identity : fourPointExternalPointVelocity coefficient positions = fun current : ℂ =>
      Complex.I * ∑ target : Fin 4, ((coefficient * fourPointSign target : ℝ) : ℂ) / star (current - positions target) :=
    funext (fourPointExternalPointVelocity_literal coefficient positions)
  rw [identity]
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro target _
  have difference : ContDiffAt ℝ 2 (fun current : ℂ => current - positions target) location := by fun_prop
  have conjugate : ContDiffAt ℝ 2 (fun current : ℂ => star (current - positions target)) location :=
    Complex.conjCLE.contDiff.contDiffAt.comp location difference
  simpa only [div_eq_mul_inv] using
    contDiffAt_const.mul (conjugate.inv (star_ne_zero.mpr (noncollision target)))

end EulerNonuniqueness.Section6
