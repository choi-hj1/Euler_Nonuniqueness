import EulerNonuniqueness.Section8.RegularizedTransportDefectBound

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem regularizedApproximation_original_transport_residual {source : Vorticity}
    (integrable : Integrable source) {horizon : ℝ} (nonnegative : 0 ≤ horizon)
    (sourceMeasurable : Measurable source) (membership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    {sourceBound : ℝ} (sourceBoundNonnegative : 0 ≤ sourceBound)
    (sourceBounded : ∀ position, ‖source position‖ ≤ sourceBound)
    {test : ℝ × Plane → ℝ} (admissible : ScalarTestOn horizon test) :
    (∀ index, Integrable (fun point : ℝ × Plane =>
      regularizedApproximation integrable nonnegative index point.1 point.2 *
        (timeDerivative test point + spatialDerivative test point
          (biotSavart (regularizedApproximation integrable nonnegative index point.1) point.2)))
            (spacetimeMeasure horizon)) ∧
      Integrable (fun position => source position * test (0, position)) ∧
      Tendsto (fun index => (∫ point : ℝ × Plane,
        regularizedApproximation integrable nonnegative index point.1 point.2 *
          (timeDerivative test point + spatialDerivative test point
            (biotSavart (regularizedApproximation integrable nonnegative index point.1) point.2))
              ∂spacetimeMeasure horizon) + (∫ position, source position * test (0, position))) atTop (𝓝 0) := by
  have regularizedTransport (index : ℕ) := regularizedApproximation_weakTransportOn integrable nonnegative
    sourceMeasurable sourceBoundNonnegative sourceBounded index test admissible
  obtain ⟨_, _, defectBounds⟩ := exists_regularizedTransportDefect_bound integrable nonnegative sourceMeasurable
    membership sourceBoundNonnegative sourceBounded admissible.1 admissible.2.1
  have split (index : ℕ) :
      (fun point : ℝ × Plane => regularizedApproximation integrable nonnegative index point.1 point.2 *
        (timeDerivative test point + spatialDerivative test point
          (biotSavart (regularizedApproximation integrable nonnegative index point.1) point.2))) =
        (fun point : ℝ × Plane => regularizedApproximation integrable nonnegative index point.1 point.2 *
          (timeDerivative test point + spatialDerivative test point
            (regularizedBiotSavart (regularizationScale index)
              (regularizedApproximation integrable nonnegative index point.1) point.2))) +
          regularizedTransportDefect integrable nonnegative test index := by
    funext point
    have differencePair : ((0 : ℝ),
        biotSavart (regularizedApproximation integrable nonnegative index point.1) point.2 -
          regularizedBiotSavart (regularizationScale index)
            (regularizedApproximation integrable nonnegative index point.1) point.2) =
        (0, biotSavart (regularizedApproximation integrable nonnegative index point.1) point.2) -
          (0, regularizedBiotSavart (regularizationScale index)
            (regularizedApproximation integrable nonnegative index point.1) point.2) := by simp
    simp only [Pi.add_apply, regularizedTransportDefect, spatialDerivative, differencePair, map_sub]
    ring
  refine ⟨?_, (regularizedTransport 0).2.1, ?_⟩
  · intro index
    rw [split index]
    exact (regularizedTransport index).1.add (defectBounds index).1
  · have residualEquals (index : ℕ) :
        (∫ point : ℝ × Plane, regularizedApproximation integrable nonnegative index point.1 point.2 *
          (timeDerivative test point + spatialDerivative test point
            (biotSavart (regularizedApproximation integrable nonnegative index point.1) point.2))
              ∂spacetimeMeasure horizon) + (∫ position, source position * test (0, position)) =
          ∫ point, regularizedTransportDefect integrable nonnegative test index point ∂spacetimeMeasure horizon := by
      rw [split index, integral_add' (regularizedTransport index).1 (defectBounds index).1]
      linarith [(regularizedTransport index).2.2]
    simpa only [residualEquals] using tendsto_integral_regularizedTransportDefect integrable nonnegative sourceMeasurable
      membership sourceBoundNonnegative sourceBounded admissible.1 admissible.2.1

end EulerNonuniqueness
