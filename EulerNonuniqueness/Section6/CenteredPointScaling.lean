import EulerNonuniqueness.Section6.FourPointCenterProjection
import EulerNonuniqueness.Section6.PointScaling

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.Section6

theorem fourPointCenterProjection_complex_mul (scale : ℂ) (positions : FourPointConfiguration) :
    fourPointCenterProjection (fun target => scale * positions target) =
      fun target => scale * fourPointCenterProjection positions target := by
  funext target
  simp only [fourPointCenterProjection, fourPointArithmeticCenter, ← Finset.mul_sum]
  ring

theorem fourPointCenteredField_physical_dilation (frequency length : ℝ) (lengthPositive : 0 < length)
    {rotation : ℂ} (rotationNorm : ‖rotation‖ = 1) (positions : FourPointConfiguration) :
    fourPointCenteredField (frequency * length ^ 2) (fun target => (length : ℂ) * rotation * positions target) =
      fun target => ((frequency * length : ℝ) : ℂ) * rotation * fourPointCenteredField 1 positions target := by
  rw [fourPointCenteredField, fourPointField_physical_dilation frequency length lengthPositive rotationNorm,
    fourPointCenterProjection_complex_mul]
  rfl

theorem centered_point_normalized_hasDerivAt {trajectory : ℝ → FourPointConfiguration}
    {forcing : FourPointConfiguration} {frequency length start time : ℝ} {rotation : ℂ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (rotationNorm : ‖rotation‖ = 1)
    (equation : HasDerivAt trajectory
      (fourPointCenteredField (frequency * length ^ 2) (trajectory (start + time / frequency)) + forcing)
      (start + time / frequency)) :
    let normalized : ℝ → FourPointConfiguration := fun current target =>
      ((length : ℂ) * rotation)⁻¹ * trajectory (start + current / frequency) target
    HasDerivAt normalized (fourPointCenteredField 1 (normalized time) +
      fun target => ((frequency : ℂ) * ((length : ℂ) * rotation))⁻¹ * forcing target) time := by
  dsimp only
  let scale : ℂ := (length : ℂ) * rotation
  have rotationNonzero : rotation ≠ 0 := norm_ne_zero_iff.mp (by rw [rotationNorm]; norm_num)
  have scaleNonzero : scale ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr lengthPositive.ne') rotationNonzero
  have frequencyNonzero : (frequency : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr frequencyPositive.ne'
  let positions : FourPointConfiguration := fun target => scale⁻¹ * trajectory (start + time / frequency) target
  have recovery : (fun target => scale * positions target) = trajectory (start + time / frequency) := by
    funext target
    simp only [positions, ← mul_assoc, mul_inv_cancel₀ scaleNonzero, one_mul]
  have field := fourPointCenteredField_physical_dilation frequency length lengthPositive rotationNorm positions
  change fourPointCenteredField (frequency * length ^ 2) (fun target => scale * positions target) = _ at field
  rw [recovery] at field
  apply hasDerivAt_pi.mpr
  intro target
  have affine := ((hasDerivAt_id time).div_const frequency).const_add start
  have derivative := ((hasDerivAt_pi.mp equation target).scomp time affine).const_mul scale⁻¹
  rw [field] at derivative
  convert derivative using 1
  simp only [Pi.add_apply, Complex.real_smul, positions, scale, Complex.ofReal_mul,
    one_div, Complex.ofReal_inv]
  field_simp [rotationNonzero, Complex.ofReal_ne_zero.mpr lengthPositive.ne', frequencyNonzero]
  <;> ring

end EulerNonuniqueness.Section6
