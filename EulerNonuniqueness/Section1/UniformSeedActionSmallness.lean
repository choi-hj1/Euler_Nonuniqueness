import EulerNonuniqueness.Section1.PolynomialSeedSmallness
import EulerNonuniqueness.Section1.UniformIntegratedReferenceIndexBudget

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_uniform_seed_action_budget_small (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {referenceConstant forcingConstant exponent tolerance : ℝ}
    (referenceNonnegative : 0 ≤ referenceConstant) (forcingNonnegative : 0 ≤ forcingConstant)
    (exponentPositive : 0 < exponent) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ, ∀ finish ∈ Icc (0 : ℝ) 1,
      let changed : Scales := {scales with frequency := frequency}
      let omega := changed.omega index
      let seed := changed.seed index ^ exponent
      let reference := referenceConstant * ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
      omega * reference * finish + omega * finish * seed +
        omega * (forcingConstant * omega * seed) * (finish ^ 2 / 2 + finish ^ 3 / 6) < tolerance := by
  have thirdPositive : 0 < tolerance / 3 := by positivity
  have scaledPositive : 0 < tolerance / (3 * (forcingConstant + 1)) := by positivity
  filter_upwards [scales.eventually_uniform_reference_index_rate_small ratioBound alphaPositive
      referenceNonnegative thirdPositive,
    scales.eventually_polynomial_seed_rpow_lt ratioBound alphaPositive 1 exponentPositive thirdPositive,
    scales.eventually_polynomial_seed_rpow_lt ratioBound alphaPositive 2 exponentPositive scaledPositive,
    eventually_gt_atTop (0 : ℝ)] with frequency referenceSmall linearSmall quadraticSmall frequencyPositive
  intro index finish inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let omega := changed.omega index
  let seed := changed.seed index ^ exponent
  let reference := referenceConstant * ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive index
  have seedNonnegative : 0 ≤ seed := Real.rpow_nonneg
    (changed.seed_pos frequencyPositive ratioPositive index).le exponent
  have referenceBound : omega * reference * finish < tolerance / 3 :=
    (mul_le_of_le_one_right (referenceSmall index).1 inside.2).trans_lt (referenceSmall index).2
  have linearBound : omega * finish * seed < tolerance / 3 := by
    have comparison := mul_le_mul_of_nonneg_right inside.2 (mul_nonneg omegaPositive.le seedNonnegative)
    have small : omega * seed < tolerance / 3 := by simpa only [pow_one] using linearSmall index
    have normalized : omega * finish * seed ≤ omega * seed := by
      simpa only [mul_assoc, mul_comm, mul_left_comm, mul_one, one_mul] using comparison
    exact normalized.trans_lt small
  have timePolynomial : finish ^ 2 / 2 + finish ^ 3 / 6 ≤ (1 : ℝ) := by
    have square := pow_le_pow_left₀ inside.1 inside.2 2
    have cube := pow_le_pow_left₀ inside.1 inside.2 3
    norm_num only [one_pow] at square cube
    linarith only [square, cube]
  have quadraticBound : omega * (forcingConstant * omega * seed) *
      (finish ^ 2 / 2 + finish ^ 3 / 6) < tolerance / 3 := by
    have larger : forcingConstant * (omega ^ 2 * seed) ≤ (forcingConstant + 1) * (omega ^ 2 * seed) := by
      nlinarith only [mul_nonneg (sq_nonneg omega) seedNonnegative]
    have small := mul_lt_mul_of_pos_left (quadraticSmall index)
      (show 0 < forcingConstant + 1 by linarith only [forcingNonnegative])
    have cancellation : (forcingConstant + 1) * (tolerance / (3 * (forcingConstant + 1))) = tolerance / 3 := by
      field_simp
      ring
    have finalSmall : (forcingConstant + 1) * (omega ^ 2 * seed) < tolerance / 3 := by
      simpa only [cancellation] using small
    have polynomialBound := mul_le_mul_of_nonneg_left timePolynomial
      (show 0 ≤ omega * (forcingConstant * omega * seed) by positivity)
    have normalized : omega * (forcingConstant * omega * seed) *
        (finish ^ 2 / 2 + finish ^ 3 / 6) ≤ forcingConstant * (omega ^ 2 * seed) := by
      convert polynomialBound using 1; ring
    exact (normalized.trans larger).trans_lt finalSmall
  change omega * reference * finish + omega * finish * seed +
    omega * (forcingConstant * omega * seed) * (finish ^ 2 / 2 + finish ^ 3 / 6) < tolerance
  linarith only [referenceBound, linearBound, quadraticBound]

end EulerNonuniqueness.Paper
