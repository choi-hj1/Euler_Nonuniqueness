import EulerNonuniqueness.Section8.RegularizedMomentCompactness
import EulerNonuniqueness.Section8.RegularizedOriginalTransport
import EulerNonuniqueness.Section8.RegularizedLimitSupport
import EulerNonuniqueness.Section8.MomentEulerLimit

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem exists_eulerSolutionOn_of_bounded_initialDatum {source : Vorticity}
    (datum : InitialDatum source) (sourceMeasurable : Measurable source)
    {sourceBound : ℝ} (boundNonnegative : 0 ≤ sourceBound)
    (bounded : ∀ position, ‖source position‖ ≤ sourceBound)
    {radius : ℝ} (supported : support source ⊆ Metric.closedBall 0 radius)
    {horizon : ℝ} (positive : 0 < horizon) :
    ∃ omega : Evolution, IsEulerSolutionOn horizon source omega ∧
      Measurable (fun point : Icc 0 horizon × Plane => omega point.1 point.2) ∧
      ∀ time ∈ Icc 0 horizon,
        support (omega time) ⊆ Metric.closedBall 0 (radius + regularizedSourceSpeed source * time) := by
  have integrable : Integrable source := memLp_one_iff_integrable.mp (by simpa using datum.2.1 1 le_rfl)
  have data := regularizedApproximation_momentCompactnessData integrable datum positive.le
  have initialConvergence : InitialLpConvergence (regularizedApproximation integrable positive.le) source := by
    refine ⟨datum.2.1, ?_⟩
    intro exponent exponentBound
    simpa only [regularizedApproximation_initial, sub_self, eLpNorm_zero] using
      (tendsto_const_nhds (x := (0 : ℝ≥0∞)))
  have residual (test : ℝ × Plane → ℝ) (admissible : ScalarTestOn horizon test) :=
    regularizedApproximation_original_transport_residual integrable positive.le sourceMeasurable
      (datum.2.1 4 (by norm_num)) boundNonnegative bounded admissible
  obtain ⟨subsequence, _, limit, path, solution⟩ := data.exists_euler_limit_of_vanishing_residual positive
    initialConvergence (fun test admissible => by
      simpa only [transportTestCoefficient] using (residual test admissible).1)
    (fun test admissible => by
      simpa only [transportTestCoefficient, regularizedApproximation_initial] using (residual test admissible).2.2)
  refine ⟨growingSupportMask radius (regularizedSourceSpeed source) limit,
    regularized_limit_mask_isEulerSolutionOn integrable positive.le (datum.2.1 4 (by norm_num)) supported path solution,
    measurable_growingSupportMask_on_time_subtype path.measurable, ?_⟩
  exact fun time _ => support_growingSupportMask_subset radius (regularizedSourceSpeed source) limit time

theorem exists_growing_support_euler_solutions_of_bounded_initialDatum {source : Vorticity}
    (datum : InitialDatum source) (sourceMeasurable : Measurable source)
    {sourceBound : ℝ} (boundNonnegative : 0 ≤ sourceBound)
    (bounded : ∀ position, ‖source position‖ ≤ sourceBound) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ horizon : ℝ, 0 < horizon →
      ∃ omega : Evolution, IsEulerSolutionOn horizon source omega ∧
        Measurable (fun point : Icc 0 horizon × Plane => omega point.1 point.2) ∧
        ∀ time ∈ Icc 0 horizon,
          support (omega time) ⊆ Metric.closedBall 0 (radius + regularizedSourceSpeed source * time) := by
  obtain ⟨radius, radiusPositive, supported⟩ := datum.exists_support_radius
  exact ⟨radius, radiusPositive, fun _ positive => exists_eulerSolutionOn_of_bounded_initialDatum datum
    sourceMeasurable boundNonnegative bounded supported positive⟩

end EulerNonuniqueness
