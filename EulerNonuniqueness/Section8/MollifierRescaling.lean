import EulerNonuniqueness.Section8.RescaledCommutator
import EulerNonuniqueness.Section8.Mollification

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem mollifierBump_rescaling (index : ℕ) (position : Plane) :
    (mollifierBump (Space := Plane) index) position =
      (mollifierBump (Space := Plane) 0) (((index : ℝ) + 1) • position) := by
  have nonzero : (index : ℝ) + 1 ≠ 0 := by positivity
  change (mollifierBump (Space := Plane) index).toFun position =
    (mollifierBump (Space := Plane) 0).toFun (((index : ℝ) + 1) • position)
  simp only [ContDiffBump.toFun, mollifierBump, Function.comp_apply, sub_zero, Nat.cast_zero, zero_add,
    div_one, smul_smul]
  congr 1
  · field_simp
  · congr 1
    field_simp <;> ring

theorem integral_mollifierBump_rescaling (index : ℕ) :
    (∫ position : Plane, (mollifierBump (Space := Plane) index) position) =
      (((index : ℝ) + 1) ^ 2)⁻¹ * ∫ position : Plane, (mollifierBump (Space := Plane) 0) position := by
  simp_rw [mollifierBump_rescaling index]
  simpa only [Complex.finrank_real_complex, smul_eq_mul] using
    Measure.integral_comp_smul_of_nonneg (volume : Measure Plane)
      (fun position => (mollifierBump (Space := Plane) 0) position) ((index : ℝ) + 1) (hR := by positivity)

theorem normed_mollifierBump_rescaling (index : ℕ) :
    (mollifierBump index).normed (volume : Measure Plane) =
      rescaledKernel ((mollifierBump 0).normed volume) (1 / ((index : ℝ) + 1)) := by
  funext position
  rw [ContDiffBump.normed_def, integral_mollifierBump_rescaling, mollifierBump_rescaling]
  simp only [rescaledKernel, one_div, inv_inv, inv_pow, ContDiffBump.normed_def]
  field_simp
  ring

theorem tendsto_integral_transportCommutator_mollifier_norm
    {vorticity : Vorticity} {radius : ℝ} (radiusNonnegative : 0 ≤ radius)
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp vorticity (ENNReal.ofReal exponent) volume)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (zeroMean : (∫ position, vorticity position) = 0) :
    Tendsto (fun index => ∫ position,
      ‖transportCommutator ((mollifierBump index).normed volume) (biotSavart vorticity) vorticity position‖)
      atTop (𝓝 0) := by
  have result := tendsto_integral_transportCommutator_rescaledKernel_norm radiusNonnegative membership
    supportBound zeroMean ((mollifierBump (Space := Plane) 0).contDiff_normed (μ := volume))
    ((mollifierBump (Space := Plane) 0).hasCompactSupport_normed (μ := volume))
    (fun index => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat
  apply result.congr'
  filter_upwards [] with index
  rw [normed_mollifierBump_rescaling index]

theorem integral_transportCommutator_mollifier_norm_le
    {vorticity : Vorticity} {radius : ℝ} (radiusNonnegative : 0 ≤ radius)
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp vorticity (ENNReal.ofReal exponent) volume)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (zeroMean : (∫ position, vorticity position) = 0) (index : ℕ) :
    Integrable (transportCommutator ((mollifierBump index).normed volume) (biotSavart vorticity) vorticity) ∧
      (∫ position, ‖transportCommutator ((mollifierBump index).normed volume)
        (biotSavart vorticity) vorticity position‖) ≤
      (∫ offset : Plane, ‖fderiv ℝ ((mollifierBump 0).normed volume) offset‖ * ‖offset‖) *
        (2 * (eLpNorm vorticity 2 volume).toReal ^ 2) := by
  rw [normed_mollifierBump_rescaling index]
  exact integral_transportCommutator_rescaledKernel_norm_le radiusNonnegative membership supportBound zeroMean
    ((mollifierBump (Space := Plane) 0).contDiff_normed (μ := volume))
    ((mollifierBump (Space := Plane) 0).hasCompactSupport_normed (μ := volume)) (by positivity)

end EulerNonuniqueness
