import EulerNonuniqueness.Section8.BoundedDatumMassExistence
import EulerNonuniqueness.Section8.ExpandingEulerSupport

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem exists_growing_support_global_eulerSolution_of_bounded_initialDatum
    {source : Vorticity} (datum : InitialDatum source) (sourceMeasurable : Measurable source)
    {sourceBound : ℝ} (boundNonnegative : 0 ≤ sourceBound)
    (bounded : ∀ position, ‖source position‖ ≤ sourceBound)
    {radius : ℝ} (radiusPositive : 0 < radius) (supported : support source ⊆ Metric.closedBall 0 radius) :
    ∃ omega : Evolution, IsEulerSolution source omega ∧
      (∀ horizon : ℝ, AEStronglyMeasurable (Function.uncurry omega) (spacetimeMeasure horizon)) ∧
      (∀ time : ℝ, 0 ≤ time → support (omega time) ⊆
        Metric.closedBall 0 (radius + regularizedSourceSpeed source * time)) ∧
      ∀ time : ℝ, 0 ≤ time → InitialDatum (omega time) := by
  have finiteExistence (index : ℕ) := exists_zeroMean_eulerSolutionOn_of_bounded_initialDatum
    datum sourceMeasurable boundNonnegative bounded supported (show (0 : ℝ) < index + 1 by positivity)
  choose sequence solutions _ growingSupport zeroMean using finiteExistence
  exact exists_growing_support_global_euler_of_expanding_solutions datum solutions zeroMean radiusPositive
    (regularizedSourceSpeed_nonnegative source) growingSupport

end EulerNonuniqueness
