import EulerNonuniqueness.Section3.FiniteLiteralPatchPassiveIntegrability
import EulerNonuniqueness.Section3.FiniteLiteralPatchTransportFTC

open Set MeasureTheory Filter
open scoped ContDiff

namespace EulerNonuniqueness.Paper

noncomputable section

theorem indicator_one_mul_eq (domain : Set ℂ) (function : ℂ → ℝ) :
    (fun position => domain.indicator (fun _ => (1 : ℝ)) position * function position) = domain.indicator function := by
  funext position
  by_cases member : position ∈ domain <;> simp [member]

namespace FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem passive_indicator_weakTransportOn (flow : FiniteLiteralPatchFlow configuration) {horizon : ℝ}
    (nonnegative : 0 ≤ horizon) (short : horizon < flow.duration) (index : Fin count) :
    WeakTransportOn horizon ((flow.domain 0 index).indicator (fun _ => (1 : ℝ)))
      (fun time => (flow.domain time index).indicator (fun _ => (1 : ℝ)))
      (fun time => biotSavart (flow.vorticity time)) := by
  intro test properties
  have main_integrable := flow.integrable_passive_transport horizon index properties.1 properties.2.1
  have initial_domain_integrable : IntegrableOn (fun position => test (0, position)) (flow.domain 0 index) :=
    affinePatchDomain_integrable_of_continuous (configuration.center index) (configuration.radius_pos index)
      (flow.shape 0 index) ((flow.nearby 0 index).trans_le (min_le_left _ _)) _
      (properties.1.continuous.comp (continuous_const.prodMk continuous_id))
  have initial_integrable : Integrable (fun position =>
      (flow.domain 0 index).indicator (fun _ => (1 : ℝ)) position * test (0, position)) := by
    rw [indicator_one_mul_eq]
    exact (integrable_indicator_iff (flow.domain_isOpen 0 index).measurableSet).mpr initial_domain_integrable
  refine ⟨main_integrable, initial_integrable, ?_⟩
  let derivative := fderiv ℝ test
  have derivative_continuous : Continuous derivative := properties.1.continuous_fderiv (by simp)
  have test_derivative : ∀ point, HasFDerivAt test (derivative point) point :=
    fun point => (properties.1.differentiable (by simp) point).hasFDerivAt
  let coefficient : ℝ × ℂ → ℝ := fun point => timeDerivative test point +
    spatialDerivative test point (biotSavart (flow.vorticity point.1) point.2)
  have inner_identity (time : ℝ) (inside : time ∈ Ioo 0 horizon) :
      (∫ position, (flow.domain time index).indicator (fun _ => (1 : ℝ)) position * coefficient (time, position)) =
        flow.fluxTransportRate index test derivative time := by
    rw [indicator_one_mul_eq, integral_indicator (flow.domain_isOpen time index).measurableSet]
    dsimp only [coefficient]
    rw [integral_add (flow.domain_test_temporal_integrable time index properties.1)
      (flow.domain_test_spatial_integrable time index properties.1 properties.2.1)]
    exact (flow.fluxTransportRate_eq_actual
      ⟨by linarith [flow.duration_positive, inside.1], inside.2.trans short⟩ index test derivative
      properties.1.continuous derivative_continuous test_derivative).symm
  have rate_identity := flow.integral_fluxTransportRate_eq_sub nonnegative short index test derivative
    properties.1.continuous derivative_continuous test_derivative
  have terminal : (∫ position in flow.domain horizon index, test (horizon, position)) = 0 := by
    simp only [properties.2.2 horizon _ le_rfl, integral_zero]
  rw [terminal, zero_sub, intervalIntegral.integral_of_le nonnegative, integral_Ioc_eq_integral_Ioo] at rate_identity
  have main_identity :
      (∫ point, (flow.domain point.1 index).indicator (fun _ => (1 : ℝ)) point.2 * coefficient point
        ∂spacetimeMeasure horizon) = -(∫ position in flow.domain 0 index, test (0, position)) := by
    calc
      _ = ∫ time in Ioo 0 horizon, ∫ position,
          (flow.domain time index).indicator (fun _ => (1 : ℝ)) position * coefficient (time, position) :=
        integral_prod _ main_integrable
      _ = ∫ time in Ioo 0 horizon, flow.fluxTransportRate index test derivative time := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with time inside
        exact inner_identity time inside
      _ = _ := rate_identity
  change (∫ point, (flow.domain point.1 index).indicator (fun _ => (1 : ℝ)) point.2 * coefficient point
    ∂spacetimeMeasure horizon) + _ = 0
  rw [main_identity, indicator_one_mul_eq, integral_indicator (flow.domain_isOpen 0 index).measurableSet]
  exact neg_add_cancel _

end FiniteLiteralPatchFlow

end

end EulerNonuniqueness.Paper
