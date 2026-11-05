import EulerNonuniqueness.Section8.TemporalTestProduct
import EulerNonuniqueness.General.TerminalBoundaryLimit
import EulerNonuniqueness.General.TerminalCutoffProduct

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace EulerNonuniqueness

theorem WeakTransportOn.terminal_test_identity {horizon : ℝ} {initial : Vorticity}
    {omega : Evolution} {velocity : ℝ → Velocity}
    (transport : WeakTransportOn horizon initial omega velocity) (positive : 0 < horizon)
    {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (mainIntegrable : Integrable (fun point : ℝ × Plane => omega point.1 point.2 *
      (timeDerivative test point + spatialDerivative test point (velocity point.1 point.2))) (spacetimeMeasure horizon))
    (momentContinuous : ContinuousOn (fun time => ∫ position, omega time position * test (time, position)) (Icc 0 horizon)) :
    Integrable (fun position => initial position * test (0, position)) ∧
      (∫ point : ℝ × Plane, omega point.1 point.2 *
        (timeDerivative test point + spatialDerivative test point (velocity point.1 point.2)) ∂spacetimeMeasure horizon) +
          (∫ position, initial position * test (0, position)) =
            ∫ position, omega horizon position * test (horizon, position) := by
  let main := fun point : ℝ × Plane => omega point.1 point.2 *
    (timeDerivative test point + spatialDerivative test point (velocity point.1 point.2))
  let weighted := fun (index : ℕ) (point : ℝ × Plane) => terminalCutoff horizon index point.1 * main point
  let boundary := fun (index : ℕ) (point : ℝ × Plane) => omega point.1 point.2 * test point * deriv (terminalCutoff horizon index) point.1
  have weightedIntegrable (index : ℕ) : Integrable (weighted index) (spacetimeMeasure horizon) := by
    simpa only [smul_eq_mul] using integrable_terminalCutoff_smul mainIntegrable horizon index
  have cutoffTransport (index : ℕ) := transport _ (scalarTestOn_terminalCutoff_product positive index smooth compact)
  have split (index : ℕ) : (fun point : ℝ × Plane => omega point.1 point.2 *
      (timeDerivative (temporalTestProduct (terminalCutoff horizon index) test) point +
        spatialDerivative (temporalTestProduct (terminalCutoff horizon index) test) point (velocity point.1 point.2))) =
          weighted index + boundary index := by
    funext point
    rw [timeDerivative_temporalTestProduct (contDiff_terminalCutoff horizon index) smooth,
      spatialDerivative_temporalTestProduct (contDiff_terminalCutoff horizon index) smooth]
    dsimp only [weighted, boundary, main, Pi.add_apply]
    ring
  have boundaryIntegrable (index : ℕ) : Integrable (boundary index) (spacetimeMeasure horizon) := by
    have whole := (cutoffTransport index).1
    rw [split index] at whole
    simpa only [Pi.add_apply, Pi.sub_apply, add_sub_cancel_left] using whole.sub (weightedIntegrable index)
  have initialIntegrable : Integrable (fun position => initial position * test (0, position)) := by
    simpa only [temporalTestProduct, terminalCutoff_at_zero positive 0, one_mul] using (cutoffTransport 0).2.1
  have cutoffIdentity (index : ℕ) :
      (∫ point, weighted index point ∂spacetimeMeasure horizon) +
        (∫ point, boundary index point ∂spacetimeMeasure horizon) +
          (∫ position, initial position * test (0, position)) = 0 := by
    have identity := (cutoffTransport index).2.2
    rw [split index, integral_add' (weightedIntegrable index) (boundaryIntegrable index)] at identity
    simpa only [temporalTestProduct, terminalCutoff_at_zero positive index, one_mul] using identity
  have boundaryFubini (index : ℕ) :
      (∫ point, boundary index point ∂spacetimeMeasure horizon) =
        ∫ time in Ioo 0 horizon, (∫ position, omega time position * test (time, position)) *
          deriv (terminalCutoff horizon index) time := by
    calc
      _ = ∫ time in Ioo 0 horizon, ∫ position, boundary index (time, position) :=
        integral_prod _ (boundaryIntegrable index)
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun time => by
          change (∫ position, (omega time position * test (time, position)) * deriv (terminalCutoff horizon index) time) = _
          rw [integral_mul_const]
  have weightedConverges : Tendsto (fun index => ∫ point, weighted index point ∂spacetimeMeasure horizon)
      atTop (𝓝 (∫ point, main point ∂spacetimeMeasure horizon)) := by
    simpa only [smul_eq_mul] using tendsto_integral_terminalCutoff_smul positive mainIntegrable
  have boundaryConverges : Tendsto (fun index => ∫ point, boundary index point ∂spacetimeMeasure horizon)
      atTop (𝓝 (-(∫ position, omega horizon position * test (horizon, position)))) := by
    simpa only [boundaryFubini] using
      EulerNonuniqueness.ContinuousOn.tendsto_integral_mul_deriv_terminalCutoff momentContinuous positive
  have sumConverges := (weightedConverges.add boundaryConverges).add
    (tendsto_const_nhds (x := ∫ position, initial position * test (0, position)))
  have zeroConverges : Tendsto (fun index =>
      (∫ point, weighted index point ∂spacetimeMeasure horizon) +
        (∫ point, boundary index point ∂spacetimeMeasure horizon) +
          (∫ position, initial position * test (0, position))) atTop (𝓝 0) := by
    simpa only [cutoffIdentity] using (tendsto_const_nhds (x := (0 : ℝ)))
  refine ⟨initialIntegrable, ?_⟩
  have equality := tendsto_nhds_unique sumConverges zeroConverges
  change (∫ point, main point ∂spacetimeMeasure horizon) + _ = _
  linarith

end EulerNonuniqueness
