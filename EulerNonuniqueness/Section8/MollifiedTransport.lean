import EulerNonuniqueness.Section8.MollifierRescaling

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff Convolution

namespace EulerNonuniqueness

theorem fderiv_scalarConvolution_apply {source kernel : Plane → ℝ}
    (integrable : Integrable source) (smooth : ContDiff ℝ ∞ kernel)
    (compact : HasCompactSupport kernel) (position direction : Plane) :
    fderiv ℝ (kernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] source) position direction =
      ∫ offset, source (position - offset) * fderiv ℝ kernel offset direction := by
  have derivative := compact.hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (smooth.of_le (by simp)) integrable.locallyIntegrable position
  rw [derivative.fderiv]
  have derivativeIntegrable := (compact.fderiv (𝕜 := ℝ)).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Plane)
    (smooth.continuous_fderiv (by simp)) integrable.locallyIntegrable position
  simp_rw [convolution_def]
  rw [ContinuousLinearMap.integral_apply derivativeIntegrable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun offset => by
    simp [ContinuousLinearMap.precompL_apply, mul_comm]

theorem transportCommutator_eq_mollifiedTransport
    {source kernel : Plane → ℝ} {velocity : Velocity}
    (sourceIntegrable : Integrable source)
    (fluxIntegrable : Integrable (fun position => source position • velocity position))
    (smooth : ContDiff ℝ ∞ kernel) (compact : HasCompactSupport kernel) (position : Plane) :
    transportCommutator kernel velocity source position =
      fderiv ℝ (kernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] source) position (velocity position) -
        ∫ offset, source (position - offset) * fderiv ℝ kernel offset (velocity (position - offset)) := by
  have firstIntegrable : Integrable (fun offset => source (position - offset) *
      fderiv ℝ kernel offset (velocity position)) := by
    have result := integrable_fderiv_apply_of_locallyIntegrable
      ((sourceIntegrable.comp_sub_left position).smul_const (velocity position)).locallyIntegrable
      (smooth.of_le (by simp)) compact
    simpa only [map_smul, smul_eq_mul] using result
  have secondIntegrable : Integrable (fun offset => source (position - offset) *
      fderiv ℝ kernel offset (velocity (position - offset))) := by
    have result := integrable_fderiv_apply_of_locallyIntegrable
      (fluxIntegrable.comp_sub_left position).locallyIntegrable (smooth.of_le (by simp)) compact
    simpa only [map_smul, smul_eq_mul] using result
  rw [fderiv_scalarConvolution_apply sourceIntegrable smooth compact,
    ← integral_sub firstIntegrable secondIntegrable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun offset => by
    simp only [transportCommutator, map_sub, mul_sub]

theorem integrable_vorticity_smul_biotSavart {vorticity : Vorticity} {radius : ℝ}
    (radiusNonnegative : 0 ≤ radius)
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp vorticity (ENNReal.ofReal exponent) volume)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (zeroMean : (∫ position, vorticity position) = 0) :
    Integrable (fun position => vorticity position • biotSavart vorticity position) := by
  have sourceIntegrable : Integrable vorticity :=
    memLp_one_iff_integrable.mp (by simpa using membership 1 le_rfl)
  have sourceMember : MemLp vorticity 2 volume := by simpa using membership 2 (by norm_num)
  have velocityMember := memLp_biotSavart_two_of_memLp_support_integral_zero
    holderConjugate_four_fourThirds (membership 4 (by norm_num)) (by norm_num)
    sourceIntegrable zeroMean radiusNonnegative supportBound
  exact memLp_one_iff_integrable.mp (velocityMember.smul sourceMember)

theorem continuous_transportCommutator {source kernel : Plane → ℝ} {velocity : Velocity}
    (sourceIntegrable : Integrable source)
    (fluxIntegrable : Integrable (fun position => source position • velocity position))
    (velocityContinuous : Continuous velocity)
    (smooth : ContDiff ℝ ∞ kernel) (compact : HasCompactSupport kernel) :
    Continuous (transportCommutator kernel velocity source) := by
  have convolutionSmooth := compact.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) smooth sourceIntegrable.locallyIntegrable
  have fluxContinuous := (compact.fderiv (𝕜 := ℝ)).continuous_convolution_left
    ((ContinuousLinearMap.apply ℝ ℝ).flip)
    (smooth.continuous_fderiv (by simp)) fluxIntegrable.locallyIntegrable
  convert ((convolutionSmooth.continuous_fderiv (by simp)).clm_apply velocityContinuous).sub fluxContinuous using 1
  funext position
  rw [transportCommutator_eq_mollifiedTransport sourceIntegrable fluxIntegrable smooth compact]
  simp only [convolution_def, ContinuousLinearMap.flip_apply, ContinuousLinearMap.apply_apply,
    map_smul, smul_eq_mul]

end EulerNonuniqueness
