import EulerNonuniqueness.Section8.BoundedDatumMassExistence
import EulerNonuniqueness.Section8.ExpandingEulerSequence

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem exists_global_eulerSolution_of_bounded_initialDatum {source : Vorticity}
    (datum : InitialDatum source) (sourceMeasurable : Measurable source)
    {sourceBound : ℝ} (boundNonnegative : 0 ≤ sourceBound)
    (bounded : ∀ position, ‖source position‖ ≤ sourceBound) :
    ∃ omega : Evolution, IsEulerSolution source omega := by
  obtain ⟨radius, radiusPositive, supported⟩ := datum.exists_support_radius
  have finiteExistence (index : ℕ) := exists_zeroMean_eulerSolutionOn_of_bounded_initialDatum
    datum sourceMeasurable boundNonnegative bounded supported (show (0 : ℝ) < index + 1 by positivity)
  choose sequence solutions _ growingSupport zeroMean using finiteExistence
  exact exists_global_euler_of_expanding_solutions datum solutions zeroMean radiusPositive
    (regularizedSourceSpeed_nonnegative source) growingSupport

end EulerNonuniqueness
