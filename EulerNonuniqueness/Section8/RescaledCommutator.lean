import EulerNonuniqueness.Section8.CommutatorConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

def rescaledKernel (kernel : Plane → ℝ) (scale : ℝ) (position : Plane) : ℝ :=
  (scale ^ 2)⁻¹ * kernel (scale⁻¹ • position)

theorem contDiff_rescaledKernel {kernel : Plane → ℝ} (smooth : ContDiff ℝ ∞ kernel) (scale : ℝ) :
    ContDiff ℝ ∞ (rescaledKernel kernel scale) :=
  contDiff_const.mul (smooth.comp (contDiff_const.smul contDiff_id))

theorem hasCompactSupport_rescaledKernel {kernel : Plane → ℝ} (compact : HasCompactSupport kernel)
    {scale : ℝ} (nonzero : scale ≠ 0) : HasCompactSupport (rescaledKernel kernel scale) := by
  have result := compact.comp_homeomorph (Homeomorph.smul (isUnit_iff_ne_zero.mpr (inv_ne_zero nonzero)).unit)
  exact result.mul_left

theorem fderiv_rescaledKernel_apply {kernel : Plane → ℝ} (smooth : ContDiff ℝ ∞ kernel)
    (scale : ℝ) (position direction : Plane) :
    fderiv ℝ (rescaledKernel kernel scale) position direction =
      (scale ^ 2)⁻¹ * fderiv ℝ kernel (scale⁻¹ • position) (scale⁻¹ • direction) := by
  have derivative := ((smooth.differentiable (by simp)).differentiableAt.hasFDerivAt.comp position
    ((hasFDerivAt_id position).const_smul scale⁻¹)).const_mul (scale ^ 2)⁻¹
  exact congrArg (fun linear : Plane →L[ℝ] ℝ => linear direction) derivative.fderiv

theorem transportCommutator_rescaledKernel_eq
    {vorticity : Vorticity} {radius : ℝ} (radiusNonnegative : 0 ≤ radius)
    (integrable : Integrable vorticity)
    (member : MemLp vorticity (ENNReal.ofReal 4) volume)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {kernel : Plane → ℝ} (smooth : ContDiff ℝ ∞ kernel) (compact : HasCompactSupport kernel)
    {scale : ℝ} (positive : 0 < scale) (position : Plane) :
    transportCommutator (rescaledKernel kernel scale) (biotSavart vorticity) vorticity position =
      scaledCenteredTransportCommutator kernel (biotSavart vorticity) vorticity scale position := by
  rw [transportCommutator_eq_centered integrable member radiusNonnegative supportBound
    (contDiff_rescaledKernel smooth scale) (hasCompactSupport_rescaledKernel compact positive.ne')]
  let integrand := fun offset => (vorticity (position - offset) - vorticity position) *
    fderiv ℝ (rescaledKernel kernel scale) offset
      (biotSavart vorticity position - biotSavart vorticity (position - offset))
  have changeVariables := Measure.integral_comp_smul_of_nonneg (volume : Measure Plane) integrand scale
    (hR := positive.le)
  have dimension : Module.finrank ℝ Plane = 2 := Complex.finrank_real_complex
  rw [dimension, smul_eq_mul] at changeVariables
  have identity : ∀ offset : Plane, integrand (scale • offset) = (scale ^ 2)⁻¹ *
      scaledCenteredTransportIntegrand kernel (biotSavart vorticity) vorticity scale offset position := by
    intro offset
    dsimp only [integrand]
    rw [fderiv_rescaledKernel_apply smooth, inv_smul_smul₀ positive.ne']
    dsimp [scaledCenteredTransportIntegrand]
    ring
  simp_rw [identity] at changeVariables
  rw [integral_const_mul] at changeVariables
  exact (mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 2 positive.ne')) changeVariables).symm

theorem tendsto_integral_transportCommutator_rescaledKernel_norm
    {vorticity : Vorticity} {radius : ℝ} (radiusNonnegative : 0 ≤ radius)
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp vorticity (ENNReal.ofReal exponent) volume)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (zeroMean : (∫ position, vorticity position) = 0)
    {kernel : Plane → ℝ} (smooth : ContDiff ℝ ∞ kernel) (compact : HasCompactSupport kernel)
    {scales : ℕ → ℝ} (positive : ∀ index, 0 < scales index)
    (scalesConverge : Tendsto scales atTop (𝓝 0)) :
    Tendsto (fun index => ∫ position,
      ‖transportCommutator (rescaledKernel kernel (scales index)) (biotSavart vorticity) vorticity position‖)
      atTop (𝓝 0) := by
  have integrable : Integrable vorticity :=
    memLp_one_iff_integrable.mp (by simpa using membership 1 le_rfl)
  simp_rw [transportCommutator_rescaledKernel_eq radiusNonnegative integrable (membership 4 (by norm_num))
    supportBound smooth compact (positive _)]
  exact tendsto_integral_scaledCenteredTransportCommutator_norm radiusNonnegative membership
    supportBound zeroMean smooth compact scalesConverge

theorem integral_transportCommutator_rescaledKernel_norm_le
    {vorticity : Vorticity} {radius : ℝ} (radiusNonnegative : 0 ≤ radius)
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp vorticity (ENNReal.ofReal exponent) volume)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (zeroMean : (∫ position, vorticity position) = 0)
    {kernel : Plane → ℝ} (smooth : ContDiff ℝ ∞ kernel) (compact : HasCompactSupport kernel)
    {scale : ℝ} (positive : 0 < scale) :
    Integrable (transportCommutator (rescaledKernel kernel scale) (biotSavart vorticity) vorticity) ∧
      (∫ position, ‖transportCommutator (rescaledKernel kernel scale) (biotSavart vorticity) vorticity position‖) ≤
        (∫ offset : Plane, ‖fderiv ℝ kernel offset‖ * ‖offset‖) *
          (2 * (eLpNorm vorticity 2 volume).toReal ^ 2) := by
  have integrable : Integrable vorticity :=
    memLp_one_iff_integrable.mp (by simpa using membership 1 le_rfl)
  have identity := funext (transportCommutator_rescaledKernel_eq radiusNonnegative integrable
    (membership 4 (by norm_num)) supportBound smooth compact positive)
  rw [identity]
  have member : MemLp vorticity 2 volume := by simpa using membership 2 (by norm_num)
  have result := integral_scaledCenteredTransportCommutator_norm_le radiusNonnegative membership
    supportBound zeroMean smooth compact scale member
  refine ⟨result.1, result.2.trans ?_⟩
  simpa only [Lp.norm_toLp] using integral_commutatorEnvelope_le smooth compact member scale

end EulerNonuniqueness
