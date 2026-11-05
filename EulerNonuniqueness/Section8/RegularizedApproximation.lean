import EulerNonuniqueness.Section8.RegularizedWeakTransport
import EulerNonuniqueness.Section8.RegularizedMomentContinuity

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction

namespace EulerNonuniqueness

def regularizationScale (index : ℕ) : ℝ := 1 / ((index : ℝ) + 1)

theorem regularizationScale_positive (index : ℕ) : 0 < regularizationScale index := by
  dsimp [regularizationScale]
  positivity

theorem tendsto_regularizationScale : Tendsto regularizationScale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def regularizedApproximationFlow {source : Vorticity} (integrable : Integrable source)
    {horizon : ℝ} (nonnegative : 0 ≤ horizon) (index : ℕ) :
    RegularizedFlowOn source integrable (regularizationScale index) (regularizationScale_positive index) horizon :=
  regularizedFlowOn integrable (regularizationScale_positive index) nonnegative

def regularizedApproximation {source : Vorticity} (integrable : Integrable source)
    {horizon : ℝ} (nonnegative : 0 ≤ horizon) : ℕ → Evolution :=
  fun index => (regularizedApproximationFlow integrable nonnegative index).vorticity

theorem regularizedApproximation_initial {source : Vorticity} (integrable : Integrable source)
    {horizon : ℝ} (nonnegative : 0 ≤ horizon) (index : ℕ) :
    regularizedApproximation integrable nonnegative index 0 = source :=
  (regularizedApproximationFlow integrable nonnegative index).vorticity_initial

theorem regularizedApproximation_weakTransportOn {source : Vorticity} (integrable : Integrable source)
    {horizon : ℝ} (nonnegative : 0 ≤ horizon) (sourceMeasurable : Measurable source)
    {sourceBound : ℝ} (boundNonnegative : 0 ≤ sourceBound) (bounded : ∀ position, ‖source position‖ ≤ sourceBound)
    (index : ℕ) :
    WeakTransportOn horizon source (regularizedApproximation integrable nonnegative index)
      (fun time => regularizedBiotSavart (regularizationScale index)
        (regularizedApproximation integrable nonnegative index time)) :=
  (regularizedApproximationFlow integrable nonnegative index).weakTransportOn nonnegative sourceMeasurable
    boundNonnegative bounded

end EulerNonuniqueness
