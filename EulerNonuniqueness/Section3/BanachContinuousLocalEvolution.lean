import EulerNonuniqueness.Section3.BanachLocalEvolution

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

theorem banach_continuous_local_evolution_of_lipschitzOn_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (field : E → E) (initial : E) {radius : ℝ} (radius_positive : 0 < radius)
    (constant : NNReal) (lipschitz : LipschitzOnWith constant field (closedBall initial radius)) :
    ∃ duration > (0 : ℝ), ∃ solution : ℝ → E,
      solution 0 = initial ∧ Continuous solution ∧ Continuous (field ∘ solution) ∧
      (∀ time, solution time ∈ closedBall initial radius) ∧
      ∀ time ∈ Ioo (-duration) duration, HasDerivAt solution (field (solution time)) time := by
  obtain ⟨duration, duration_positive, original, initial_eq, stays, equation⟩ :=
    banach_local_evolution_of_lipschitzOn_ball field initial radius_positive constant lipschitz
  let shorter := duration / 2
  have shorter_positive : 0 < shorter := by dsimp [shorter]; positivity
  have ordered : -shorter ≤ shorter := by linarith
  let projection : ℝ → Icc (-shorter) shorter := projIcc (-shorter) shorter ordered
  let solution : ℝ → E := fun time => original (projection time)
  have original_continuous : ContinuousOn original (Icc (-shorter) shorter) := by
    intro time inside
    apply (equation time ?_).continuousAt.continuousWithinAt
    dsimp [shorter] at inside
    constructor <;> linarith [inside.1, inside.2]
  have solution_continuous : Continuous solution :=
    original_continuous.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun time => (projection time).property)
  have solution_stays (time : ℝ) : solution time ∈ closedBall initial radius := stays (projection time)
  have initial_projection : (projection 0 : ℝ) = 0 := by
    exact congrArg Subtype.val (projIcc_of_mem ordered ⟨by linarith, by linarith⟩)
  refine ⟨shorter, shorter_positive, solution, ?_, solution_continuous,
    lipschitz.continuousOn.comp_continuous solution_continuous solution_stays, solution_stays, ?_⟩
  · change original (projection 0) = initial
    rw [initial_projection, initial_eq]
  · intro time inside
    have original_inside : time ∈ Ioo (-duration) duration := by
      dsimp [shorter] at inside
      constructor <;> linarith [inside.1, inside.2]
    have agrees : solution =ᶠ[𝓝 time] original := by
      filter_upwards [Icc_mem_nhds inside.1 inside.2] with current current_inside
      change original (projection current) = original current
      congr 1
      exact congrArg Subtype.val (projIcc_of_mem ordered current_inside)
    have point_agrees : solution time = original time := agrees.eq_of_nhds
    rw [point_agrees]
    exact (equation time original_inside).congr_of_eventuallyEq agrees

end

end EulerNonuniqueness.Paper
