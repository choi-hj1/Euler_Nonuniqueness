import EulerNonuniqueness.Section8.RegularizedLagrangianIntegrability

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction ContDiff

namespace EulerNonuniqueness.RegularizedFlowOn

theorem weakTransportOn {source : Vorticity} {integrable : Integrable source}
    {scale horizon : ℝ} {positive : 0 < scale}
    (flow : RegularizedFlowOn source integrable scale positive horizon)
    (nonnegative : 0 ≤ horizon) (sourceMeasurable : Measurable source)
    {sourceBound : ℝ} (sourceBoundNonnegative : 0 ≤ sourceBound)
    (sourceBounded : ∀ position, ‖source position‖ ≤ sourceBound) :
    WeakTransportOn horizon source flow.vorticity
      (fun time => regularizedBiotSavart scale (flow.vorticity time)) := by
  intro test testProperties
  obtain ⟨mainIntegrable, initialIntegrable⟩ := flow.integrable_transport_terms nonnegative sourceMeasurable
    sourceBoundNonnegative sourceBounded testProperties.1 testProperties.2.1
  have lagrangianIntegrable := flow.integrable_lagrangian_transport nonnegative sourceMeasurable
    testProperties.1 testProperties.2.1
  refine ⟨mainIntegrable, initialIntegrable, ?_⟩
  let coefficient := fun point : ℝ × Plane => timeDerivative test point + spatialDerivative test point
    (regularizedBiotSavart scale (flow.vorticity point.1) point.2)
  have mainIdentity : (∫ point, flow.vorticity point.1 point.2 * coefficient point ∂spacetimeMeasure horizon) =
      -(∫ position, source position * test (0, position)) := by
    calc
      _ = ∫ time in Ioo 0 horizon, ∫ position, flow.vorticity time position * coefficient (time, position) :=
        integral_prod _ mainIntegrable
      _ = ∫ time in Ioo 0 horizon, ∫ label, source label * coefficient (time, flow.particleMap time label) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with time inside
        simpa only [smul_eq_mul] using flow.integral_vorticity_smul nonnegative ⟨inside.1.le, inside.2.le⟩
          (fun position => coefficient (time, position))
      _ = ∫ label, ∫ time in Ioo 0 horizon, source label * coefficient (time, flow.particleMap time label) :=
        integral_integral_swap lagrangianIntegrable
      _ = _ := by
        rw [← integral_neg]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun label => by
          dsimp only
          rw [integral_const_mul]
          have characteristic := flow.characteristic_test_FTC nonnegative
            (testProperties.1.of_le (by simp))
            (fun position => testProperties.2.2 horizon position le_rfl) label
          have coefficientIdentity : (∫ time in Ioo 0 horizon, coefficient (time, flow.particleMap time label)) =
              -test (0, label) := by
            change (∫ time in Ioo 0 horizon, coefficient (time, flow.particleMap time label)) + test (0, label) = 0 at characteristic
            linarith
          rw [coefficientIdentity, mul_neg]
  change (∫ point, flow.vorticity point.1 point.2 * coefficient point ∂spacetimeMeasure horizon) + _ = 0
  rw [mainIdentity]
  exact neg_add_cancel _

end EulerNonuniqueness.RegularizedFlowOn
