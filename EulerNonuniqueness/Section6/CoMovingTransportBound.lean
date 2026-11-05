import EulerNonuniqueness.Section6.CoMovingTransportSymmetry
import EulerNonuniqueness.Section6.PatchExternalCentroidLaw

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Section6

theorem integral_vorticity_star_kernel_difference {vorticity : Vorticity}
    (integrable : Integrable vorticity) (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume)
    (center position : ℂ) :
    (∫ source : ℂ, vorticity source • star (biotSavartKernel (center - source) - biotSavartKernel (position - source))) =
      star (biotSavart vorticity center - biotSavart vorticity position) := by
  have firstIntegrable := integrable_biotSavart_integrand_of_L1_L4 integrable membership center
  have secondIntegrable := integrable_biotSavart_integrand_of_L1_L4 integrable membership position
  rw [biotSavart, biotSavart, ← integral_sub firstIntegrable secondIntegrable]
  simp only [Complex.star_def]
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun source => by
    simp only [Complex.real_smul, map_sub, map_mul, Complex.conj_ofReal]
    ring

theorem integral_coMovingVorticityPair_inner {vorticity : Vorticity}
    (integrable : Integrable vorticity) (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume)
    (center position : ℂ) (power : ℕ) :
    (∫ source : ℂ, coMovingVorticityPair vorticity center power (position, source)) =
      vorticity position • (star (biotSavart vorticity center - biotSavart vorticity position) *
        (star (center - position))⁻¹ ^ power) := by
  simp only [coMovingVorticityPair, ← smul_mul_assoc]
  rw [integral_mul_const, integral_smul, integral_vorticity_star_kernel_difference integrable membership]

theorem coMoving_transport_integral_symmetrization {vorticity : Vorticity}
    (integrable : Integrable vorticity) (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume)
    {radius bound distance : ℝ}
    (supported : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (bounded : ∀ position, |vorticity position| ≤ bound)
    (center : ℂ) (positive : 0 < distance)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖) (power : ℕ) :
    (∫ position : ℂ, vorticity position •
      (star (biotSavart vorticity center - biotSavart vorticity position) * (star (center - position))⁻¹ ^ power)) =
      -(Complex.I / ((4 * Real.pi : ℝ) : ℂ)) *
        ∫ pair : ℂ × ℂ, vorticity pair.1 •
          (vorticity pair.2 • coMovingInversePowerKernel power (center - pair.1) (center - pair.2)) ∂volume.prod volume := by
  have joint := integrable_coMovingVorticityPair integrable supported bounded center positive separated power
  have identity := integral_coMovingVorticityPair_symmetrization integrable supported bounded center positive separated power
  rw [integral_prod _ joint] at identity
  simpa only [integral_coMovingVorticityPair_inner integrable membership] using identity

theorem integrable_coMoving_transport {vorticity : Vorticity}
    (integrable : Integrable vorticity) (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume)
    {radius bound distance : ℝ}
    (supported : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (bounded : ∀ position, |vorticity position| ≤ bound)
    (center : ℂ) (positive : 0 < distance)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖) (power : ℕ) :
    Integrable (fun position : ℂ => vorticity position •
      (star (biotSavart vorticity center - biotSavart vorticity position) * (star (center - position))⁻¹ ^ power)) := by
  have joint := integrable_coMovingVorticityPair integrable supported bounded center positive separated power
  simpa only [integral_coMovingVorticityPair_inner integrable membership] using joint.integral_prod_left

theorem norm_coMoving_transport_integral_bound {vorticity : Vorticity}
    (integrable : Integrable vorticity) (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume)
    {radius bound distance : ℝ}
    (supported : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (bounded : ∀ position, |vorticity position| ≤ bound)
    (center : ℂ) (positive : 0 < distance)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖) (power : ℕ) :
    ‖∫ position : ℂ, vorticity position •
      (star (biotSavart vorticity center - biotSavart vorticity position) * (star (center - position))⁻¹ ^ (power + 3))‖ ≤
      ((((power + 3 : ℝ) * 2 ^ (power + 2) + 10) * distance⁻¹ ^ power) / (4 * Real.pi)) *
        (∫ position, inverseSquareVorticityWeight vorticity center position) ^ 2 := by
  rw [coMoving_transport_integral_symmetrization integrable membership supported bounded center positive separated,
    norm_mul, norm_neg, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have joint := integrable_weighted_coMovingInversePowerKernel integrable center positive separated power
  have estimate := norm_integral_weighted_coMovingInversePowerKernel integrable center positive separated power
  rw [← integral_prod _ joint] at estimate
  exact (mul_le_mul_of_nonneg_left estimate (by positivity : 0 ≤ 1 / (4 * Real.pi))).trans_eq (by ring)

end EulerNonuniqueness.Section6
