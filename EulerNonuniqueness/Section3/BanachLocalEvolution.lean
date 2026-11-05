import EulerNonuniqueness.Section3.ContourLocalEvolution

open Set Metric

namespace EulerNonuniqueness.Paper

noncomputable section

theorem banach_local_evolution_of_lipschitzOn_ball {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (field : E → E) (initial : E) {radius : ℝ}
    (radius_pos : 0 < radius) (constant : NNReal)
    (lipschitz : LipschitzOnWith constant field (closedBall initial radius)) :
    ∃ duration > (0 : ℝ), ∃ solution : ℝ → E,
      solution 0 = initial ∧ (∀ time, solution time ∈ closedBall initial radius) ∧
      ∀ time ∈ Ioo (-duration) duration, HasDerivAt solution (field (solution time)) time := by
  let speed : NNReal := ⟨(constant : ℝ) * radius + ‖field initial‖ + 1, by positivity⟩
  have speed_pos : 0 < (speed : ℝ) := by dsimp only [speed, NNReal.coe_mk]; positivity
  let duration := radius / (speed : ℝ)
  have duration_pos : 0 < duration := div_pos radius_pos speed_pos
  have initial_mem : initial ∈ closedBall initial radius := mem_closedBall_self radius_pos.le
  have hypotheses : IsPicardLindelof (fun _ => field) (-duration) 0 duration initial constant radius speed := by
    refine {
      ht₀ := ⟨(by linarith), duration_pos.le⟩
      hR := radius_pos.le
      lipschitz := fun _ _ => lipschitz
      cont := fun _ _ => continuousOn_const
      norm_le := ?_
      C_mul_le_R := ?_ }
    · intro time time_mem value value_mem
      have bound := lipschitz.dist_le_mul value value_mem initial initial_mem
      have distance_bound : dist value initial ≤ radius := value_mem
      have norm_bound : ‖field value‖ ≤ dist (field value) (field initial) + ‖field initial‖ := by
        rw [dist_eq_norm]
        calc
          _ = ‖(field value - field initial) + field initial‖ := by rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      have scaled_bound := mul_le_mul_of_nonneg_left distance_bound constant.property
      apply norm_bound.trans
      apply (add_le_add_right (bound.trans scaled_bound) ‖field initial‖).trans
      exact le_add_of_nonneg_right zero_le_one
    · simp only [sub_zero, zero_sub, neg_neg, max_self]
      dsimp only [duration]
      rw [mul_div_cancel₀ radius (ne_of_gt speed_pos)]
  let problem : PicardLindelof E := {
    toFun := fun _ => field
    tMin := -duration
    tMax := duration
    t₀ := ⟨0, hypotheses.ht₀⟩
    x₀ := initial
    C := speed
    R := ⟨radius, radius_pos.le⟩
    L := constant
    isPicardLindelof := hypotheses }
  obtain ⟨solution, initial_eq, stays, equation⟩ := picard_exists_solution_in_closedBall problem
  refine ⟨duration, duration_pos, solution, initial_eq, stays, ?_⟩
  intro time time_mem
  exact (equation time ⟨time_mem.1.le, time_mem.2.le⟩).hasDerivAt
    (Icc_mem_nhds time_mem.1 time_mem.2)

end

end EulerNonuniqueness.Paper
