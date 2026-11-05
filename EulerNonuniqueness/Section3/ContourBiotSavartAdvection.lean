import EulerNonuniqueness.Section3.RegularizedContourAdvection
import EulerNonuniqueness.Section3.DomainBiotSavartLimit
import EulerNonuniqueness.Section8.UniformVelocityBounds

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

theorem tendsto_regularizedBiotSavart_pointwise
    {scales : ℕ → ℝ} (positive : ∀ index, 0 < scales index)
    (convergence : Tendsto scales atTop (𝓝 0)) {source : Vorticity}
    (integrable : Integrable source) (membership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    (point : ℂ) :
    Tendsto (fun index => regularizedBiotSavart (scales index) source point) atTop
      (𝓝 (biotSavart source point)) := by
  have uniform_convergence := tendstoUniformly_regularizedBiotSavart_sub (Parameter := Unit)
    positive convergence (vorticity := fun _ _ => source)
    (fun _ _ => integrable) (fun _ _ => membership)
    (oneBound := ∫ position, ‖source position‖)
    (fourBound := (eLpNorm source (ENNReal.ofReal (4 : ℝ)) volume).toReal)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  have pointwise := (uniform_convergence.tendsto_at ((), point)).add_const (biotSavart source point)
  simpa only [sub_add_cancel, zero_add] using pointwise

theorem norm_contourAreaPair_le (first second : ℂ) :
    ‖contourAreaPair first second‖ ≤ ‖first‖ * ‖second‖ := by
  exact (Complex.abs_im_le_norm (star first * second)).trans_eq (by simp [norm_mul])

theorem integral_nearCircleInterior_biotSavart_advection
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (function : ℂ → ℝ) (derivative : ℂ → ℂ →L[ℝ] ℝ)
    (function_continuous : Continuous function) (derivative_continuous : Continuous derivative)
    (function_derivative : ∀ position, HasFDerivAt function (derivative position) position)
    {source : Vorticity} (integrable : Integrable source)
    (membership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume) :
    (∫ position in nearCircleInterior data small, derivative position (biotSavart source position)) =
      ∫ label in (-Real.pi)..Real.pi, function (data.val.1 label) *
        contourAreaPair (biotSavart source (data.val.1 label)) (data.val.2.val.1 label) := by
  let scales : ℕ → ℝ := fun index => 1 / ((index : ℝ) + 1)
  have positive (index : ℕ) : 0 < scales index := by dsimp [scales]; positivity
  have convergence : Tendsto scales atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let bound : ℝ := (eLpNorm source (ENNReal.ofReal (4 : ℝ)) volume).toReal *
    (eLpNorm ((Metric.ball (0 : ℂ) 1).indicator biotSavartKernel)
      (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal +
        (∫ position, ‖source position‖) * (1 / (2 * Real.pi))
  have bounded (index : ℕ) (position : ℂ) : ‖regularizedBiotSavart (scales index) source position‖ ≤ bound :=
    norm_regularizedBiotSavart_le_L1_L4 (positive index) integrable membership position
  have field_continuous (index : ℕ) : Continuous (regularizedBiotSavart (scales index) source) :=
    continuous_iff_continuousAt.mpr fun position =>
      (regularizedBiotSavart_hasFDerivAt (positive index) integrable position).continuousAt
  have field_convergence (position : ℂ) :=
    tendsto_regularizedBiotSavart_pointwise positive convergence integrable membership position
  have interior_convergence : Tendsto
      (fun index => ∫ position in nearCircleInterior data small,
        derivative position (regularizedBiotSavart (scales index) source position)) atTop
      (𝓝 (∫ position in nearCircleInterior data small, derivative position (biotSavart source position))) := by
    apply tendsto_integral_of_dominated_convergence (fun position => ‖derivative position‖ * bound)
    · intro index
      exact (derivative_continuous.clm_apply (field_continuous index)).aestronglyMeasurable
    · exact nearCircleInterior_integrable_of_continuous data small _
        (derivative_continuous.norm.mul continuous_const)
    · intro index
      exact Eventually.of_forall fun position =>
        ((derivative position).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (bounded index position) (norm_nonneg _))
    · exact Eventually.of_forall fun position =>
        (derivative position).continuous.continuousAt.tendsto.comp (field_convergence position)
  have boundary_convergence_restricted : Tendsto
      (fun index => ∫ label in uIoc (-Real.pi) Real.pi, function (data.val.1 label) *
        contourAreaPair (regularizedBiotSavart (scales index) source (data.val.1 label)) (data.val.2.val.1 label)) atTop
      (𝓝 (∫ label in uIoc (-Real.pi) Real.pi, function (data.val.1 label) *
        contourAreaPair (biotSavart source (data.val.1 label)) (data.val.2.val.1 label))) := by
    apply tendsto_integral_of_dominated_convergence
      (fun label => ‖function (data.val.1 label)‖ * (bound * ‖data.val.2.val.1 label‖))
    · intro index
      have continuous_integrand : Continuous (fun label => function (data.val.1 label) *
          contourAreaPair (regularizedBiotSavart (scales index) source (data.val.1 label)) (data.val.2.val.1 label)) :=
        (function_continuous.comp data.val.1.continuous).mul
          (continuous_contourAreaPair.comp (((field_continuous index).comp data.val.1.continuous).prodMk
            data.val.2.val.1.continuous))
      exact continuous_integrand.aestronglyMeasurable
    · have continuous_bound : Continuous (fun label =>
          ‖function (data.val.1 label)‖ * (bound * ‖data.val.2.val.1 label‖)) :=
        (function_continuous.comp data.val.1.continuous).norm.mul
          (continuous_const.mul data.val.2.val.1.continuous.norm)
      exact (continuous_bound.intervalIntegrable (-Real.pi) Real.pi).def'
    · intro index
      exact Eventually.of_forall fun label => by
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (norm_contourAreaPair_le _ _).trans
          (mul_le_mul_of_nonneg_right (bounded index _) (norm_nonneg _))
    · exact Eventually.of_forall fun label =>
        ((continuous_contourAreaPair.tendsto _).comp
          ((field_convergence (data.val.1 label)).prodMk_nhds tendsto_const_nhds)).const_mul _
  have boundary_convergence : Tendsto
      (fun index => ∫ label in (-Real.pi)..Real.pi, function (data.val.1 label) *
        contourAreaPair (regularizedBiotSavart (scales index) source (data.val.1 label)) (data.val.2.val.1 label)) atTop
      (𝓝 (∫ label in (-Real.pi)..Real.pi, function (data.val.1 label) *
        contourAreaPair (biotSavart source (data.val.1 label)) (data.val.2.val.1 label))) := by
    simpa only [intervalIntegral.intervalIntegral_eq_integral_uIoc] using
      boundary_convergence_restricted.const_smul (if -Real.pi ≤ Real.pi then (1 : ℝ) else -1)
  apply tendsto_nhds_unique interior_convergence
  convert boundary_convergence using 1
  funext index
  exact integral_nearCircleInterior_regularized_advection data small function derivative
    function_continuous derivative_continuous function_derivative (positive index) integrable

end

end EulerNonuniqueness.Paper
