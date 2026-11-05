import EulerNonuniqueness.Section1.Scales

noncomputable section

namespace EulerNonuniqueness.Paper

theorem Scales.omega_ge_frequency (scales : Scales) (frequencyPositive : 0 < scales.frequency)
    (ratioBound : 1 ≤ scales.ratio) (index : ℕ) : scales.frequency ≤ scales.omega index := by
  exact le_mul_of_one_le_right frequencyPositive.le (one_le_pow₀ ratioBound)

theorem Scales.length_le_one (scales : Scales) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : ℕ) : scales.length index ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr (Real.rpow_nonneg (scales.omega_pos frequencyPositive ratioPositive index).le _)

theorem Scales.location_le_one (scales : Scales) (index : ℕ) : scales.location index ≤ 1 := by
  rw [scales.location_eq_inv_pow]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

theorem Scales.radius_uniform_bound (scales : Scales) (amplitudePositive : 0 < scales.amplitude)
    (frequencyPositive : 0 < scales.frequency) (ratioBound : 1 ≤ scales.ratio) (index : ℕ) :
    scales.radius index ≤ Real.sqrt (2 / (scales.amplitude * scales.frequency ^ 3)) := by
  have omegaBound := scales.omega_ge_frequency frequencyPositive ratioBound index
  have lengthBound := scales.length_le_one frequencyPositive (zero_lt_one.trans_le ratioBound) index
  have numeratorBound : 2 * scales.length index ^ 2 ≤ 2 := by
    nlinarith [(scales.length_pos index).le]
  have denominatorPositive : 0 < scales.amplitude * scales.frequency ^ 3 := by positivity
  have denominatorBound : scales.amplitude * scales.frequency ^ 3 ≤ scales.amplitude * scales.omega index ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ frequencyPositive.le omegaBound 3) amplitudePositive.le
  exact Real.sqrt_le_sqrt (div_le_div₀ (by norm_num) numeratorBound denominatorPositive denominatorBound)

end EulerNonuniqueness.Paper
