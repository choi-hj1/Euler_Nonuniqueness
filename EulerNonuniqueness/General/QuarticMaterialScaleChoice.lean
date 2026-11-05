import EulerNonuniqueness.General.QuarticCubicScaleChoice

namespace EulerNonuniqueness.General

theorem quartic_frequency_material_amplitude_small
    {forcingConstant scaleRoot frequency : ℝ}
    (forcingNonnegative : 0 ≤ forcingConstant) (rootLarge : 8 ≤ scaleRoot)
    (frequencyLarge : 1 ≤ frequency) :
    forcingConstant * frequency ^ 2 / (scaleRoot ^ 3 * frequency ^ 4) ≤
      ((forcingConstant + 1) / (scaleRoot ^ 2 * frequency ^ 2)) / 8 := by
  have rootPositive : 0 < scaleRoot := by linarith
  have frequencyPositive : 0 < frequency := by linarith
  have base := quartic_frequency_primitive_small forcingNonnegative rootLarge (le_refl (1 : ℝ))
  norm_num only [one_pow, mul_one] at base
  have scaled := div_le_div_of_nonneg_right base (sq_nonneg frequency)
  convert scaled using 1 <;> field_simp [rootPositive.ne', frequencyPositive.ne'] <;> ring <;> simp

theorem quartic_frequency_quadratic_forcing_ratio
    {forcingConstant radiusCoefficient scaleRoot frequency : ℝ}
    (forcingNonnegative : 0 ≤ forcingConstant) (coefficientNonnegative : 0 ≤ radiusCoefficient)
    (rootLarge : 1 ≤ scaleRoot) (frequencyLarge : 1 ≤ frequency) :
    (forcingConstant * frequency) * (radiusCoefficient / (scaleRoot ^ 2 * frequency ^ 2)) ≤
      forcingConstant * radiusCoefficient / scaleRoot := by
  have rootPositive : 0 < scaleRoot := by linarith
  have frequencyPositive : 0 < frequency := by linarith
  have denominator : scaleRoot ≤ scaleRoot ^ 2 * frequency := by
    have square : scaleRoot ≤ scaleRoot ^ 2 := by nlinarith
    exact square.trans (le_mul_of_one_le_right (sq_nonneg scaleRoot) frequencyLarge)
  have actual := div_le_div_of_nonneg_left (mul_nonneg forcingNonnegative coefficientNonnegative)
    rootPositive denominator
  convert actual using 1 <;> field_simp [rootPositive.ne', frequencyPositive.ne'] <;> ring

theorem quartic_frequency_higher_mode_ratio
    {forcingConstant geometricConstant scaleRoot frequency ratio : ℝ}
    (forcingNonnegative : 0 ≤ forcingConstant) (frequencyPositive : 0 < frequency)
    (rootPositive : 0 < scaleRoot) (small : ratio ≤ geometricConstant / (scaleRoot * frequency)) :
    (forcingConstant * frequency) * ratio ≤ forcingConstant * geometricConstant / scaleRoot := by
  have actual := mul_le_mul_of_nonneg_left small (mul_nonneg forcingNonnegative frequencyPositive.le)
  convert actual using 1 <;> field_simp [rootPositive.ne', frequencyPositive.ne'] <;> ring

theorem quartic_frequency_cubic_ratio
    {radiusCoefficient scaleRoot frequency : ℝ}
    (rootNonzero : scaleRoot ≠ 0) (frequencyNonzero : frequency ≠ 0) :
    (scaleRoot ^ 3 * frequency ^ 4) * (radiusCoefficient / (scaleRoot ^ 2 * frequency ^ 2)) ^ 2 =
      radiusCoefficient ^ 2 / scaleRoot := by
  field_simp
  <;> ring

end EulerNonuniqueness.General
