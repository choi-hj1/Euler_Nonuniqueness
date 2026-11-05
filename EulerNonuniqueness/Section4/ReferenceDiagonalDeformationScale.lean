import EulerNonuniqueness.Section4.ReferenceDiagonalFromImpulse
import EulerNonuniqueness.Section1.UniformScaleBounds
import EulerNonuniqueness.Section1.ExternalFieldScaleBounds

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.reference_diagonal_deformation_cost_le (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioBound : 1 ≤ scales.ratio) (index : ℕ) {deformation bound : ℝ}
    (nonnegative : 0 ≤ deformation) (estimate : deformation ≤ bound / scales.omega index ^ 2) :
    48 * deformation ^ 2 / (scales.amplitude * scales.omega index ^ 3) ≤
      48 * bound ^ 2 / (scales.amplitude * scales.frequency ^ 7) := by
  have ratioPositive : 0 < scales.ratio := zero_lt_one.trans_le ratioBound
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive index
  have squareEstimate := pow_le_pow_left₀ nonnegative estimate 2
  have first := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left squareEstimate (by norm_num : (0 : ℝ) ≤ 48))
    (by positivity : 0 ≤ scales.amplitude * scales.omega index ^ 3)
  have identity : 48 * (bound / scales.omega index ^ 2) ^ 2 /
      (scales.amplitude * scales.omega index ^ 3) =
      48 * bound ^ 2 / (scales.amplitude * scales.omega index ^ 7) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
    ring
  rw [identity] at first
  exact first.trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ frequencyPositive.le
      (scales.omega_ge_frequency frequencyPositive ratioBound index) 7) amplitudePositive.le))

theorem Scales.eventually_reference_diagonal_numeric (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) (constant bound : ℝ) :
    ∀ᶠ frequency : ℝ in atTop,
      2 * constant * (({scales with frequency := frequency}).strain +
          ({scales with frequency := frequency}).hessian) +
        48 * bound ^ 2 / (scales.amplitude * frequency ^ 7) < 1 / 4 := by
  have fieldLimit := ((scales.strain_tendsto_zero ratioBound alphaPositive).add
    (scales.hessian_tendsto_zero ratioBound alphaPositive)).const_mul (2 * constant)
  have powerLimit := (tendsto_inv_atTop_zero : Tendsto (fun frequency : ℝ => frequency⁻¹) atTop (𝓝 0)).pow 7
  have errorLimit := powerLimit.const_mul (48 * bound ^ 2 / scales.amplitude)
  have totalLimit := fieldLimit.add errorLimit
  simp only [add_zero, zero_add, mul_zero, zero_pow (by norm_num : (7 : ℕ) ≠ 0)] at totalLimit
  have small := totalLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  convert small using 1 <;> simp only [zero_add, mul_zero, zero_pow (by norm_num : (7 : ℕ) ≠ 0), div_eq_mul_inv, mul_inv_rev, inv_pow]
  congr 1
  ext frequency
  ring

end EulerNonuniqueness.Paper
