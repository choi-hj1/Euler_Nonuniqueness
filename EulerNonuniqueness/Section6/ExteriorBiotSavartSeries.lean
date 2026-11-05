import EulerNonuniqueness.Section6.ExteriorKernelSeries
import EulerNonuniqueness.Section6.PatchExternalCentroidLaw
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Section6

theorem exteriorKernelSeries_weighted_bound {vorticity : Vorticity} (center normalized : ℂ)
    {radius distance : ℝ} (radiusPositive : 0 < radius) (positive : 0 < distance)
    (separated : ∀ source ∈ Function.support vorticity, distance ≤ ‖center - source‖)
    (power : ℕ) (source : ℂ) :
    ‖vorticity source • (exteriorKernelCoefficient radius power (center - source) *
      (star normalized) ^ (power + 1))‖ ≤
      (radius * ‖normalized‖ / distance) ^ power *
        (‖normalized‖ / (2 * Real.pi) * inverseSquareVorticityWeight vorticity center source) := by
  have inverseBound := exterior_inverse_power_weight_bound center positive separated power source
  have identity : vorticity source • (exteriorKernelCoefficient radius power (center - source) *
      (star normalized) ^ (power + 1)) =
      (((-1 : ℂ) ^ (power + 1) * Complex.I * (radius : ℂ) ^ power / ((2 * Real.pi : ℝ) : ℂ)) *
        (star normalized) ^ (power + 1)) *
        (vorticity source • (star (center - source))⁻¹ ^ (power + 2)) := by
    unfold exteriorKernelCoefficient
    simp only [Complex.real_smul]
    ring
  rw [identity, norm_mul]
  have scaled := mul_le_mul_of_nonneg_left inverseBound
    (norm_nonneg (((-1 : ℂ) ^ (power + 1) * Complex.I * (radius : ℂ) ^ power /
      ((2 * Real.pi : ℝ) : ℂ)) * (star normalized) ^ (power + 1)))
  apply scaled.trans_eq
  simp only [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos radiusPositive, norm_star, one_mul,
    div_pow, mul_pow, pow_succ, inv_pow]
  norm_num [abs_of_pos Real.pi_pos]
  ring

theorem exterior_biotSavart_series_hasSum {vorticity : Vorticity}
    (integrable : Integrable vorticity) (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume)
    (center normalized : ℂ) {radius distance : ℝ} (radiusPositive : 0 < radius) (positive : 0 < distance)
    (separated : ∀ source ∈ Function.support vorticity, distance ≤ ‖center - source‖)
    (small : radius * ‖normalized‖ / distance < 1) :
    HasSum (fun power : ℕ => exteriorVorticityCoefficient vorticity center radius power *
      (star normalized) ^ (power + 1))
      ((radius : ℂ)⁻¹ * (biotSavart vorticity (center + (radius : ℂ) * normalized) - biotSavart vorticity center)) := by
  let terms : ℕ → ℂ → ℂ := fun power source => vorticity source •
    (exteriorKernelCoefficient radius power (center - source) * (star normalized) ^ (power + 1))
  let bound : ℕ → ℂ → ℝ := fun power source => (radius * ‖normalized‖ / distance) ^ power *
    (‖normalized‖ / (2 * Real.pi) * inverseSquareVorticityWeight vorticity center source)
  have geometric := summable_geometric_of_lt_one (by positivity : 0 ≤ radius * ‖normalized‖ / distance) small
  have measurableTerms : ∀ power, AEStronglyMeasurable (terms power) volume := by
    intro power
    have kernelMeasurable : Measurable (fun source : ℂ =>
        exteriorKernelCoefficient radius power (center - source) * (star normalized) ^ (power + 1)) := by
      unfold exteriorKernelCoefficient
      fun_prop
    exact integrable.aestronglyMeasurable.smul kernelMeasurable.aestronglyMeasurable
  have summableBound : ∀ source, Summable (fun power => bound power source) :=
    fun source => geometric.mul_right _
  have integrableBound : Integrable (fun source => ∑' power, bound power source) := by
    simp only [bound, tsum_mul_right]
    exact (integrable_inverseSquareVorticityWeight integrable center positive separated).const_mul
      ((∑' power : ℕ, (radius * ‖normalized‖ / distance) ^ power) * (‖normalized‖ / (2 * Real.pi))) |>.congr
        (Filter.Eventually.of_forall fun source => by ring)
  have pointwise : ∀ source, HasSum (fun power => terms power source)
      (vorticity source • ((radius : ℂ)⁻¹ *
        (biotSavartKernel (center + (radius : ℂ) * normalized - source) - biotSavartKernel (center - source)))) := by
    intro source
    by_cases zero : vorticity source = 0
    · simp only [terms, zero, zero_smul]
      exact hasSum_zero
    have series := HasSum.const_smul (vorticity source)
      (exteriorKernelSeries_hasSum radiusPositive (center - source) normalized
        (((div_lt_one positive).mp small).trans_le (separated source (Function.mem_support.mpr zero))))
    convert series using 1
    congr 3
    abel
  have series := hasSum_integral_of_dominated_convergence bound measurableTerms
    (fun power => Filter.Eventually.of_forall (exteriorKernelSeries_weighted_bound center normalized radiusPositive positive separated power))
    (Filter.Eventually.of_forall summableBound) integrableBound (Filter.Eventually.of_forall pointwise)
  have termIntegral (power : ℕ) : (∫ source, terms power source) =
      exteriorVorticityCoefficient vorticity center radius power * (star normalized) ^ (power + 1) := by
    unfold terms exteriorKernelCoefficient exteriorVorticityCoefficient
    rw [← integral_const_mul, ← integral_mul_const]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun source => by
      simp only [Complex.real_smul]
      ring
  have totalIntegral : (∫ source : ℂ, vorticity source • ((radius : ℂ)⁻¹ *
        (biotSavartKernel (center + (radius : ℂ) * normalized - source) - biotSavartKernel (center - source)))) =
      (radius : ℂ)⁻¹ * (biotSavart vorticity (center + (radius : ℂ) * normalized) - biotSavart vorticity center) := by
    rw [biotSavart, biotSavart, ← integral_sub
      (integrable_biotSavart_integrand_of_L1_L4 integrable membership _)
      (integrable_biotSavart_integrand_of_L1_L4 integrable membership _), ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun source => by
      simp only [Complex.real_smul]
      ring
  simpa only [termIntegral, totalIntegral] using series

end EulerNonuniqueness.Section6
