import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Sequences

namespace EulerNonuniqueness.General

noncomputable section

open Filter
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

def continuousVectorSubmodule (action : ℝ → Space →L[ℝ] Space) : Submodule ℝ Space where
  carrier := {vector | Continuous (fun parameter => action parameter vector)}
  zero_mem' := by
    change Continuous (fun parameter => action parameter 0)
    simpa only [map_zero] using (continuous_const : Continuous (fun _ : ℝ => (0 : Space)))
  add_mem' := by
    intro first second firstContinuous secondContinuous
    change Continuous (fun parameter => action parameter (first + second))
    simpa only [map_add] using firstContinuous.add secondContinuous
  smul_mem' := by
    intro scalar vector vectorContinuous
    change Continuous (fun parameter => action parameter (scalar • vector))
    simpa only [map_smul] using vectorContinuous.const_smul scalar

theorem continuousVectorSubmodule_closed (action : ℝ → Space →L[ℝ] Space)
    (contraction : ∀ parameter vector, ‖action parameter vector‖ ≤ ‖vector‖) :
    IsClosed (continuousVectorSubmodule action : Set Space) := by
  apply IsSeqClosed.isClosed
  intro sequence limit membership converges
  have uniform : TendstoUniformly (fun index parameter => action parameter (sequence index))
      (fun parameter => action parameter limit) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro epsilon positive
    have close := (Metric.tendsto_nhds.mp converges) epsilon positive
    filter_upwards [close] with index closeIndex parameter
    calc
      dist (action parameter limit) (action parameter (sequence index)) = ‖action parameter (limit - sequence index)‖ := by
        rw [dist_eq_norm, map_sub]
      _ ≤ ‖limit - sequence index‖ := contraction parameter _
      _ < epsilon := by simpa only [← dist_eq_norm, dist_comm limit] using closeIndex
  exact uniform.continuous (Eventually.of_forall membership)

end

end EulerNonuniqueness.General
