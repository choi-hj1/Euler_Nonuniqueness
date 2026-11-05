import EulerNonuniqueness.Section3.MovingMaterialPatchTransportIntegrability
import EulerNonuniqueness.Section3.PassiveTransportScaling

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff

namespace EulerNonuniqueness.Paper.MovingMaterialPatch

theorem passive_indicator_weakTransportOn (path : MovingMaterialPatch) {horizon : ℝ}
    (nonnegative : 0 ≤ horizon) (initialInside : path.initialTime < 0) (finalInside : horizon < path.finalTime)
    (source : ℝ → Vorticity)
    (sourceIntegrable : ∀ time ∈ Icc 0 horizon, Integrable (source time))
    (sourceMembership : ∀ time ∈ Icc 0 horizon, MemLp (source time) (ENNReal.ofReal (4 : ℝ)) volume)
    (material : ∀ time ∈ Icc 0 horizon, ∀ label,
      path.boundaryVelocity time label = biotSavart (source time) (path.boundary time label))
    (velocityMeasurable : Measurable (fun point : ℝ × ℂ => biotSavart (source point.1) point.2))
    {speed : ℝ} (speedNonnegative : 0 ≤ speed)
    (speedBound : ∀ time ∈ Ioo 0 horizon, ∀ position, ‖biotSavart (source time) position‖ ≤ speed) :
    WeakTransportOn horizon ((path.domain 0).indicator (fun _ => (1 : ℝ)))
      (fun time => (path.domain time).indicator (fun _ => (1 : ℝ))) (fun time => biotSavart (source time)) := by
  intro test properties
  have mainIntegrable := path.integrable_passive_transport source velocityMeasurable speedNonnegative speedBound
    properties.1 properties.2.1
  have initialDomainIntegrable : IntegrableOn (fun position => test (0, position)) (path.domain 0) := path.integral_continuous_function 0
    (properties.1.continuous.comp (continuous_const.prodMk continuous_id))
  have initialIntegrable : Integrable
      (fun position => (path.domain 0).indicator (fun _ => (1 : ℝ)) position * test (0, position)) := by
    rw [indicator_one_mul_eq]
    exact (integrable_indicator_iff (path.domain_isOpen 0).measurableSet).mpr initialDomainIntegrable
  refine ⟨mainIntegrable, initialIntegrable, ?_⟩
  let derivative := fderiv ℝ test
  have derivativeContinuous : Continuous derivative := properties.1.continuous_fderiv (by simp)
  have testDerivative : ∀ point, HasFDerivAt test (derivative point) point :=
    fun point => (properties.1.differentiable (by simp) point).hasFDerivAt
  let coefficient : ℝ × ℂ → ℝ := fun point => timeDerivative test point +
    spatialDerivative test point (biotSavart (source point.1) point.2)
  have innerIdentity (time : ℝ) (inside : time ∈ Ioo 0 horizon) :
      (∫ position, (path.domain time).indicator (fun _ => (1 : ℝ)) position * coefficient (time, position)) =
        path.fluxTransportRate test derivative time := by
    have closedInside : time ∈ Icc 0 horizon := ⟨inside.1.le, inside.2.le⟩
    rw [indicator_one_mul_eq, integral_indicator (path.domain_isOpen time).measurableSet]
    dsimp only [coefficient]
    rw [integral_add (path.domain_test_temporal_integrable time properties.1)
      (path.domain_test_spatial_integrable time (sourceIntegrable time closedInside)
        (sourceMembership time closedInside) properties.1 properties.2.1)]
    exact (path.fluxTransportRate_eq_actual ⟨initialInside.trans inside.1, inside.2.trans finalInside⟩
      (sourceIntegrable time closedInside) (sourceMembership time closedInside) (material time closedInside)
      test derivative properties.1.continuous derivativeContinuous testDerivative).symm
  have rateIdentity := path.integral_fluxTransportRate_eq_sub nonnegative initialInside finalInside test derivative
    properties.1.continuous derivativeContinuous testDerivative
  have terminal : (∫ position in path.domain horizon, test (horizon, position)) = 0 := by
    simp only [properties.2.2 horizon _ le_rfl, integral_zero]
  rw [terminal, zero_sub, intervalIntegral.integral_of_le nonnegative, integral_Ioc_eq_integral_Ioo] at rateIdentity
  have mainIdentity :
      (∫ point, (path.domain point.1).indicator (fun _ => (1 : ℝ)) point.2 * coefficient point
        ∂spacetimeMeasure horizon) = -(∫ position in path.domain 0, test (0, position)) := by
    calc
      _ = ∫ time in Ioo 0 horizon, ∫ position,
          (path.domain time).indicator (fun _ => (1 : ℝ)) position * coefficient (time, position) :=
        integral_prod _ mainIntegrable
      _ = ∫ time in Ioo 0 horizon, path.fluxTransportRate test derivative time := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with time inside
        exact innerIdentity time inside
      _ = _ := rateIdentity
  change (∫ point, (path.domain point.1).indicator (fun _ => (1 : ℝ)) point.2 * coefficient point
    ∂spacetimeMeasure horizon) + _ = 0
  rw [mainIdentity, indicator_one_mul_eq, integral_indicator (path.domain_isOpen 0).measurableSet]
  exact neg_add_cancel _

theorem passive_density_weakTransportOn (path : MovingMaterialPatch) {horizon : ℝ}
    (nonnegative : 0 ≤ horizon) (initialInside : path.initialTime < 0) (finalInside : horizon < path.finalTime)
    (source : ℝ → Vorticity)
    (sourceIntegrable : ∀ time ∈ Icc 0 horizon, Integrable (source time))
    (sourceMembership : ∀ time ∈ Icc 0 horizon, MemLp (source time) (ENNReal.ofReal (4 : ℝ)) volume)
    (material : ∀ time ∈ Icc 0 horizon, ∀ label,
      path.boundaryVelocity time label = biotSavart (source time) (path.boundary time label))
    (velocityMeasurable : Measurable (fun point : ℝ × ℂ => biotSavart (source point.1) point.2))
    {speed : ℝ} (speedNonnegative : 0 ≤ speed)
    (speedBound : ∀ time ∈ Ioo 0 horizon, ∀ position, ‖biotSavart (source time) position‖ ≤ speed)
    (density : ℝ) :
    WeakTransportOn horizon ((path.domain 0).indicator (fun _ => density))
      (fun time => (path.domain time).indicator (fun _ => density)) (fun time => biotSavart (source time)) := by
  have result := weakTransportOn_const_mul (path.passive_indicator_weakTransportOn nonnegative initialInside finalInside
    source sourceIntegrable sourceMembership material velocityMeasurable speedNonnegative speedBound) density
  convert result using 1
  · funext position
    by_cases member : position ∈ path.domain 0 <;> simp [member]
  · funext time position
    by_cases member : position ∈ path.domain time <;> simp [member]

end EulerNonuniqueness.Paper.MovingMaterialPatch
