import Mathlib.Analysis.ODE.Gronwall

noncomputable section

open Set
open scoped NNReal Topology

namespace EulerNonuniqueness

theorem injective_flow_of_lipschitz_ODE {Space : Type*}
    [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    {field flow : ℝ → Space → Space} {horizon : ℝ} {bound : ℝ≥0}
    (lipschitz : ∀ time, LipschitzWith bound (field time))
    (initial : ∀ position, flow 0 position = position)
    (continuous : ∀ position, ContinuousOn (fun time => flow time position) (Icc 0 horizon))
    (equation : ∀ position time, time ∈ Icc 0 horizon →
      HasDerivWithinAt (fun next => flow next position)
        (field time (flow time position)) (Icc 0 horizon) time)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) : Function.Injective (flow time) := by
  intro first second equal
  have subset : Icc 0 time ⊆ Icc 0 horizon := Icc_subset_Icc_right inside.2
  have derivative (position : Space) (next : ℝ) (nextInside : next ∈ Ioc 0 time) :
      HasDerivWithinAt (fun other => flow other position)
        (field next (flow next position)) (Iic next) next := by
    have horizonInside : next ∈ Ioc 0 horizon := ⟨nextInside.1, nextInside.2.trans inside.2⟩
    exact (equation position next ⟨horizonInside.1.le, horizonInside.2⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLE_of_mem horizonInside)
  have agreement := ODE_solution_unique_of_mem_Icc_left
    (s := fun _ => (univ : Set Space))
    (fun next _ => (lipschitz next).lipschitzOnWith)
    ((continuous first).mono subset) (derivative first) (fun _ _ => mem_univ _)
    ((continuous second).mono subset) (derivative second) (fun _ _ => mem_univ _) equal
  simpa only [initial] using agreement (show (0 : ℝ) ∈ Icc 0 time from ⟨le_rfl, inside.1⟩)

end EulerNonuniqueness
