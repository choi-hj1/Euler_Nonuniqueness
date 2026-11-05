import EulerNonuniqueness.Section3.AffinePatchGreen
import EulerNonuniqueness.Section3.ContourFluxConvergence

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

theorem integral_affinePatchDomain_biotSavart_advection
    (center : ℂ) {radius : ℝ} (positive : 0 < radius) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (function : ℂ → ℝ) (derivative : ℂ → ℂ →L[ℝ] ℝ)
    (function_continuous : Continuous function) (derivative_continuous : Continuous derivative)
    (function_derivative : ∀ position, HasFDerivAt function (derivative position) position)
    {source : Vorticity} (integrable : Integrable source)
    (membership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume) :
    (∫ position in affinePatchDomain center radius data small, derivative position (biotSavart source position)) =
      ∫ label in (-Real.pi)..Real.pi, function (center + radius • data.val.1 label) *
        contourAreaPair (biotSavart source (center + radius • data.val.1 label)) (radius • data.val.2.val.1 label) := by
  let scales : ℕ → ℝ := fun index => 1 / ((index : ℝ) + 1)
  have scale_positive (index : ℕ) : 0 < scales index := by dsimp [scales]; positivity
  have convergence : Tendsto scales atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let bound : ℝ := (eLpNorm source (ENNReal.ofReal (4 : ℝ)) volume).toReal *
    (eLpNorm ((Metric.ball (0 : ℂ) 1).indicator biotSavartKernel)
      (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal +
        (∫ position, ‖source position‖) * (1 / (2 * Real.pi))
  have bounded (index : ℕ) (position : ℂ) : ‖regularizedBiotSavart (scales index) source position‖ ≤ bound :=
    norm_regularizedBiotSavart_le_L1_L4 (scale_positive index) integrable membership position
  have field_continuous (index : ℕ) : Continuous (regularizedBiotSavart (scales index) source) :=
    continuous_iff_continuousAt.mpr fun position =>
      (regularizedBiotSavart_hasFDerivAt (scale_positive index) integrable position).continuousAt
  have field_convergence (position : ℂ) :=
    tendsto_regularizedBiotSavart_pointwise scale_positive convergence integrable membership position
  have interior_convergence : Tendsto
      (fun index => ∫ position in affinePatchDomain center radius data small,
        derivative position (regularizedBiotSavart (scales index) source position)) atTop
      (𝓝 (∫ position in affinePatchDomain center radius data small, derivative position (biotSavart source position))) := by
    apply tendsto_integral_of_dominated_convergence (fun position => ‖derivative position‖ * bound)
    · intro index
      exact (derivative_continuous.clm_apply (field_continuous index)).aestronglyMeasurable
    · exact affinePatchDomain_integrable_of_continuous center positive data small _
        (derivative_continuous.norm.mul continuous_const)
    · intro index
      exact Eventually.of_forall fun position =>
        ((derivative position).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (bounded index position) (norm_nonneg _))
    · exact Eventually.of_forall fun position =>
        (derivative position).continuous.continuousAt.tendsto.comp (field_convergence position)
  have boundary_convergence := tendsto_intervalIntegral_contourFlux
    (fun label => center + radius • data.val.1 label) (fun label => radius • data.val.2.val.1 label)
    (continuous_const.add (continuous_const.smul data.val.1.continuous))
    (continuous_const.smul data.val.2.val.1.continuous)
    function function_continuous (fun index => regularizedBiotSavart (scales index) source)
    (biotSavart source) field_continuous field_convergence bound bounded (-Real.pi) Real.pi
  apply tendsto_nhds_unique interior_convergence
  convert boundary_convergence using 1
  funext index
  exact integral_affinePatchDomain_directional_field center positive data small function derivative
    function_continuous derivative_continuous function_derivative
    (regularizedBiotSavart (scales index) source) (regularizedContourVelocityDerivative (scales index) source)
    (field_continuous index) (regularizedContourVelocityDerivative_continuous (scale_positive index) integrable)
    (regularizedBiotSavart_hasFDerivAt (scale_positive index) integrable)
    (regularizedContourVelocityDerivative_trace_zero (scale_positive index) integrable)

end

end EulerNonuniqueness.Paper
