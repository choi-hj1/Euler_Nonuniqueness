import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.HausdorffDistance

noncomputable section

open Set Metric

namespace EulerNonuniqueness.General

theorem infDist_lower_bound_of_displacement {Space : Type*} [PseudoMetricSpace Space]
    (admissible : Set Space) {initial current : Space} {margin displacement : ℝ}
    (initialMargin : margin + displacement ≤ infDist initial admissibleᶜ)
    (movement : dist current initial ≤ displacement) : margin ≤ infDist current admissibleᶜ := by
  have comparison := (lipschitz_infDist_pt admissibleᶜ).dist_le_mul initial current
  rw [Real.dist_eq, NNReal.coe_one, one_mul] at comparison
  have difference := (le_abs_self (infDist initial admissibleᶜ - infDist current admissibleᶜ)).trans comparison
  rw [dist_comm initial current] at difference
  linarith

theorem trajectory_displacement_le_of_hasDerivAt_bound
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    {curve velocity : ℝ → Space} {backwardHorizon forwardHorizon bound : ℝ}
    (backwardPositive : 0 < backwardHorizon)
    (equation : ∀ time ∈ Ioo (-backwardHorizon) forwardHorizon, HasDerivAt curve (velocity time) time)
    (bounded : ∀ time ∈ Ioo (-backwardHorizon) forwardHorizon, ‖velocity time‖ ≤ bound)
    {time : ℝ} (nonnegative : 0 ≤ time) (beforeFinal : time < forwardHorizon) :
    ‖curve time - curve 0‖ ≤ bound * time := by
  have subset : Icc 0 time ⊆ Ioo (-backwardHorizon) forwardHorizon := by
    intro current inside
    exact ⟨(neg_neg_of_pos backwardPositive).trans_le inside.1, inside.2.trans_lt beforeFinal⟩
  have estimate := (convex_Icc (0 : ℝ) time).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun current inside => (equation current (subset inside)).hasDerivWithinAt)
    (fun current inside => bounded current (subset inside))
    (show (0 : ℝ) ∈ Icc 0 time from ⟨le_rfl, nonnegative⟩)
    (show time ∈ Icc 0 time from ⟨nonnegative, le_rfl⟩)
  simpa only [sub_zero, Real.norm_eq_abs, abs_of_nonneg nonnegative] using estimate

end EulerNonuniqueness.General
