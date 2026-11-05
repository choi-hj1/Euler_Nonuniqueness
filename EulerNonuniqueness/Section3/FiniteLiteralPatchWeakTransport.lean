import EulerNonuniqueness.Section3.FiniteLiteralPatchTransportFTC
import EulerNonuniqueness.Section3.FiniteLiteralPatchTestSlices
import EulerNonuniqueness.Section3.FiniteLiteralPatchIntegration

open Set MeasureTheory Filter
open scoped ContDiff

namespace EulerNonuniqueness.Paper

noncomputable section

namespace FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem weakTransportOn (flow : FiniteLiteralPatchFlow configuration) {horizon : ℝ}
    (nonnegative : 0 ≤ horizon) (short : horizon < flow.duration) :
    WeakTransportOn horizon (flow.vorticity 0) flow.vorticity (fun time => biotSavart (flow.vorticity time)) := by
  intro test properties
  obtain ⟨main_integrable, initial_integrable⟩ := flow.integrable_transport_terms horizon properties.1 properties.2.1
  refine ⟨main_integrable, initial_integrable, ?_⟩
  let derivative := fderiv ℝ test
  have derivative_continuous : Continuous derivative := properties.1.continuous_fderiv (by simp)
  have test_derivative : ∀ point, HasFDerivAt test (derivative point) point :=
    fun point => (properties.1.differentiable (by simp) point).hasFDerivAt
  let coefficient : ℝ × ℂ → ℝ := fun point => timeDerivative test point +
    spatialDerivative test point (biotSavart (flow.vorticity point.1) point.2)
  let rate : ℝ → ℝ := fun time => ∑ index, configuration.density index *
    flow.fluxTransportRate index test derivative time
  have inner_identity (time : ℝ) (inside : time ∈ Ioo 0 horizon) :
      (∫ position, flow.vorticity time position * coefficient (time, position)) = rate time := by
    rw [flow.integral_vorticity_mul time (fun position => coefficient (time, position))
      (fun index => flow.domain_test_integrable time index properties.1 properties.2.1)]
    apply Finset.sum_congr rfl
    intro index _
    congr 1
    dsimp only [coefficient]
    rw [integral_add (flow.domain_test_temporal_integrable time index properties.1)
      (flow.domain_test_spatial_integrable time index properties.1 properties.2.1)]
    exact (flow.fluxTransportRate_eq_actual
      ⟨by linarith [flow.duration_positive, inside.1], inside.2.trans short⟩
      index test derivative properties.1.continuous derivative_continuous test_derivative).symm
  have initial_identity : (∫ position, flow.vorticity 0 position * test (0, position)) =
      ∑ index, configuration.density index * ∫ position in flow.domain 0 index, test (0, position) := by
    apply flow.integral_vorticity_mul
    intro index
    exact affinePatchDomain_integrable_of_continuous (configuration.center index) (configuration.radius_pos index)
      (flow.shape 0 index) ((flow.nearby 0 index).trans_le (min_le_left _ _)) _
      (properties.1.continuous.comp (continuous_const.prodMk continuous_id))
  have rate_integral : (∫ time in (0 : ℝ)..horizon, rate time) =
      -(∫ position, flow.vorticity 0 position * test (0, position)) := by
    dsimp only [rate]
    rw [intervalIntegral.integral_finset_sum (fun index _ =>
      (continuous_const.mul (flow.continuous_fluxTransportRate index test derivative
        properties.1.continuous derivative_continuous)).intervalIntegrable 0 horizon)]
    simp_rw [intervalIntegral.integral_const_mul]
    have term_identity (index : Fin count) :
        (∫ time in (0 : ℝ)..horizon, flow.fluxTransportRate index test derivative time) =
          -(∫ position in flow.domain 0 index, test (0, position)) := by
      rw [flow.integral_fluxTransportRate_eq_sub nonnegative short index test derivative
        properties.1.continuous derivative_continuous test_derivative]
      have terminal : (∫ position in flow.domain horizon index, test (horizon, position)) = 0 := by
        simp only [properties.2.2 horizon _ le_rfl, integral_zero]
      rw [terminal, zero_sub]
    simp_rw [term_identity, mul_neg]
    rw [initial_identity, Finset.sum_neg_distrib]
  have main_identity : (∫ point, flow.vorticity point.1 point.2 * coefficient point ∂spacetimeMeasure horizon) =
      -(∫ position, flow.vorticity 0 position * test (0, position)) := by
    calc
      _ = ∫ time in Ioo 0 horizon, ∫ position, flow.vorticity time position * coefficient (time, position) :=
        integral_prod _ main_integrable
      _ = ∫ time in Ioo 0 horizon, rate time := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with time inside
        exact inner_identity time inside
      _ = ∫ time in (0 : ℝ)..horizon, rate time := by
        rw [intervalIntegral.integral_of_le nonnegative, integral_Ioc_eq_integral_Ioo]
      _ = _ := rate_integral
  change (∫ point, flow.vorticity point.1 point.2 * coefficient point ∂spacetimeMeasure horizon) + _ = 0
  rw [main_identity]
  exact neg_add_cancel _

end FiniteLiteralPatchFlow

end

end EulerNonuniqueness.Paper
