import Mathlib.Tactic

namespace EulerNonuniqueness.General

theorem quartic_geometric_ratio_le
    {scaleRoot frequency radius length : ℝ}
    (rootLarge : 1 ≤ scaleRoot) (frequencyLarge : 1 ≤ frequency)
    (radiusNonnegative : 0 ≤ radius) (lengthPositive : 0 < length)
    (square : radius ^ 2 = 2 * length ^ 2 / (scaleRoot ^ 3 * frequency ^ 3)) :
    radius / (length / 400) ≤ 1000 / (scaleRoot * frequency) := by
  have rootPositive : 0 < scaleRoot := by linarith
  have frequencyPositive : 0 < frequency := by linarith
  have ratioNonnegative : 0 ≤ radius / (length / 400) := by positivity
  have targetNonnegative : 0 ≤ 1000 / (scaleRoot * frequency) := by positivity
  apply (sq_le_sq₀ ratioNonnegative targetNonnegative).mp
  have identity : (radius / (length / 400)) ^ 2 = 320000 / (scaleRoot ^ 3 * frequency ^ 3) := by
    rw [div_pow, square]
    field_simp [rootPositive.ne', frequencyPositive.ne', lengthPositive.ne']
    <;> ring
  rw [identity, div_pow]
  apply (div_le_div_iff₀ (by positivity : 0 < scaleRoot ^ 3 * frequency ^ 3)
    (by positivity : 0 < (scaleRoot * frequency) ^ 2)).mpr
  have productLarge : 1 ≤ scaleRoot * frequency := one_le_mul_of_one_le_of_one_le rootLarge frequencyLarge
  have factor : 320000 ≤ 1000000 * (scaleRoot * frequency) := by linarith
  have actual := mul_le_mul_of_nonneg_right factor (sq_nonneg (scaleRoot * frequency))
  convert actual using 1 <;> ring

end EulerNonuniqueness.General
