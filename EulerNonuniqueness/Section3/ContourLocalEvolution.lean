import EulerNonuniqueness.Section3.ContourBanachLipschitz
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall

open Set Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 500000

local instance contourEvolutionHolderNormedSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance contourEvolutionC1NormedSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

theorem picard_exists_solution_in_closedBall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (field : PicardLindelof E) :
    ∃ solution : ℝ → E, solution field.t₀ = field.x₀ ∧
      (∀ time, solution time ∈ closedBall field.x₀ field.R) ∧
      ∀ time ∈ Icc field.tMin field.tMax,
        HasDerivWithinAt solution (field time (solution time))
          (Icc field.tMin field.tMax) time := by
  obtain ⟨iterate, fixed⟩ := field.exists_fixed
  refine ⟨iterate ∘ field.proj, ?_, ?_, ?_⟩
  · simp only [Function.comp_apply, field.proj_coe, iterate.map_t₀]
  · intro time
    exact iterate.mem_closedBall (field.proj time)
  · intro time time_mem
    simp only [Function.comp_apply, field.proj_of_mem time_mem]
    lift time to Icc field.tMin field.tMax using time_mem
    simpa only [fixed, field.proj_coe] using iterate.hasDerivWithinAt_next time

def extendedContourVelocity (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  if small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) then
    contourVelocityBanach data small else 0

theorem extendedContourVelocity_eq (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    extendedContourVelocity data = contourVelocityBanach data small := by
  simp only [extendedContourVelocity, dif_pos small]

theorem extendedContourVelocity_lipschitzOn {radius : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi))) :
    LipschitzOnWith ⟨contourVelocityBanachLipschitzConstant radius,
      contourVelocityBanachLipschitzConstant_nonneg radius_nonneg radius_small⟩
      extendedContourVelocity (closedBall standardCircleBanach radius) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro first first_mem second second_mem
  have first_near : ‖first - standardCircleBanach‖ ≤ radius := by
    exact (dist_eq_norm first standardCircleBanach) ▸ first_mem
  have second_near : ‖second - standardCircleBanach‖ ≤ radius := by
    exact (dist_eq_norm second standardCircleBanach) ▸ second_mem
  rw [extendedContourVelocity_eq first (first_near.trans_lt radius_small),
    extendedContourVelocity_eq second (second_near.trans_lt radius_small)]
  rw [dist_eq_norm (contourVelocityBanach first _) (contourVelocityBanach second _),
    dist_eq_norm first second]
  exact contourVelocityBanach_parameter_norm_bound first second radius_nonneg radius_small first_near second_near

set_option maxHeartbeats 1000000 in
theorem contour_local_evolution_in_ball (initial : PeriodicC1HolderHalf) {radius spaceRadius : ℝ}
    (radius_nonneg : 0 ≤ radius) (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (space_pos : 0 < spaceRadius)
    (contained : spaceRadius + ‖initial - standardCircleBanach‖ ≤ radius) :
    ∃ duration > (0 : ℝ), ∃ solution : ℝ → PeriodicC1HolderHalf,
      solution 0 = initial ∧
      (∀ time, ‖solution time - initial‖ ≤ spaceRadius) ∧
      (∀ time, ‖solution time - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) ∧
      ∀ time ∈ Ioo (-duration) duration,
        HasDerivAt solution (extendedContourVelocity (solution time)) time := by
  have bound_nonneg : 0 ≤ contourVelocityBanachBound radius := by
    apply le_trans (b := (radius + 3) / 2)
    · positivity
    · exact le_max_left _ _
  let speed : NNReal := ⟨contourVelocityBanachBound radius + 1, by positivity⟩
  have speed_pos : 0 < (speed : ℝ) := by dsimp [speed]; positivity
  let duration := spaceRadius / (speed : ℝ)
  have duration_pos : 0 < duration := div_pos space_pos speed_pos
  have ball_contained : closedBall initial spaceRadius ⊆ closedBall standardCircleBanach radius := by
    intro data data_mem
    have data_dist : dist data initial ≤ spaceRadius := data_mem
    have initial_dist : dist initial standardCircleBanach = ‖initial - standardCircleBanach‖ :=
      dist_eq_norm initial standardCircleBanach
    exact (dist_triangle data initial standardCircleBanach).trans
      ((add_le_add_right data_dist _).trans (initial_dist ▸ contained))
  let constant : NNReal := ⟨contourVelocityBanachLipschitzConstant radius,
    contourVelocityBanachLipschitzConstant_nonneg radius_nonneg radius_small⟩
  have hypotheses : IsPicardLindelof (fun _ => extendedContourVelocity)
      (-duration) 0 duration initial constant spaceRadius speed := by
    refine {
      ht₀ := ⟨(by linarith), duration_pos.le⟩
      hR := space_pos.le
      lipschitz := ?_
      cont := ?_
      norm_le := ?_
      C_mul_le_R := ?_ }
    · intro time time_mem
      exact (extendedContourVelocity_lipschitzOn radius_nonneg radius_small).mono ball_contained
    · intro data data_mem
      exact continuousOn_const
    · intro time time_mem data data_mem
      have near : ‖data - standardCircleBanach‖ ≤ radius :=
        (dist_eq_norm data standardCircleBanach) ▸ ball_contained data_mem
      rw [extendedContourVelocity_eq data (near.trans_lt radius_small)]
      exact (contourVelocityBanach_uniform_norm_bound data radius_nonneg radius_small near).trans
        (by dsimp [speed]; linarith)
    · simp only [sub_zero, zero_sub, neg_neg, max_self]
      dsimp only [duration]
      rw [mul_div_cancel₀ spaceRadius (ne_of_gt speed_pos)]
  let problem : PicardLindelof PeriodicC1HolderHalf :=
    { toFun := fun _ => extendedContourVelocity
      tMin := -duration
      tMax := duration
      t₀ := ⟨0, hypotheses.ht₀⟩
      x₀ := initial
      C := speed
      R := ⟨spaceRadius, space_pos.le⟩
      L := constant
      isPicardLindelof := hypotheses }
  obtain ⟨solution, initial_eq, stays, equation⟩ := picard_exists_solution_in_closedBall problem
  refine ⟨duration, duration_pos, solution, initial_eq, ?_, ?_, ?_⟩
  · intro time
    exact (dist_eq_norm (solution time) initial) ▸ stays time
  · intro time
    have near : ‖solution time - standardCircleBanach‖ ≤ radius :=
      (dist_eq_norm (solution time) standardCircleBanach) ▸ ball_contained (stays time)
    exact near.trans_lt radius_small
  · intro time time_mem
    exact (equation time ⟨time_mem.1.le, time_mem.2.le⟩).hasDerivAt
      (Icc_mem_nhds time_mem.1 time_mem.2)

theorem contour_local_evolution (initial : PeriodicC1HolderHalf)
    (small : ‖initial - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    ∃ duration > (0 : ℝ), ∃ solution : ℝ → PeriodicC1HolderHalf,
      solution 0 = initial ∧
      (∀ time, ‖solution time - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) ∧
      ∀ time ∈ Ioo (-duration) duration,
        HasDerivAt solution (extendedContourVelocity (solution time)) time := by
  let margin := min 1 (2 / (3 * Real.pi)) - ‖initial - standardCircleBanach‖
  have margin_pos : 0 < margin := sub_pos.mpr small
  let radius := ‖initial - standardCircleBanach‖ + margin / 2
  have radius_nonneg : 0 ≤ radius := by dsimp only [radius]; positivity
  have radius_small : radius < min 1 (2 / (3 * Real.pi)) := by dsimp only [radius, margin]; linarith
  obtain ⟨duration, duration_pos, solution, initial_eq, stays, nearby, equation⟩ :=
    contour_local_evolution_in_ball initial radius_nonneg radius_small
      (show 0 < margin / 2 by positivity) (show margin / 2 + ‖initial - standardCircleBanach‖ ≤ radius by dsimp only [radius]; linarith)
  exact ⟨duration, duration_pos, solution, initial_eq, nearby, equation⟩

def contourLabelEvaluation (label : ℝ) : PeriodicC1HolderHalf →L[ℝ] ℂ := by
  let evaluation : PeriodicC1HolderHalf →ₗ[ℝ] ℂ := {
    toFun := fun data => data.val.1 label
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  exact LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf) (F := ℂ)
    evaluation 1 (fun data => by
    change ‖data.val.1 label‖ ≤ 1 * ‖data‖
    simpa only [one_mul] using PeriodicC1HolderHalf.value_bound data label)

set_option maxHeartbeats 1000000 in
theorem contour_local_material_evolution (initial : PeriodicC1HolderHalf)
    (small : ‖initial - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    ∃ duration > (0 : ℝ), ∃ solution : ℝ → PeriodicC1HolderHalf,
      solution 0 = initial ∧
      (∀ time, ‖solution time - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) ∧
      ∀ time ∈ Ioo (-duration) duration, ∀ label : ℝ,
        HasDerivAt (fun time => (solution time).val.1 label)
          (contourVelocity (solution time).val.1 (solution time).val.2.val.1
            label (-Real.pi) Real.pi) time := by
  obtain ⟨duration, duration_pos, solution, initial_eq, nearby, equation⟩ :=
    contour_local_evolution initial small
  refine ⟨duration, duration_pos, solution, initial_eq, nearby, ?_⟩
  intro time time_mem label
  have derivative := ((contourLabelEvaluation label).hasFDerivAt (x := solution time)).comp_hasDerivAt time
    (equation time time_mem)
  rw [extendedContourVelocity_eq (solution time) (nearby time)] at derivative
  exact derivative

set_option maxHeartbeats 1000000 in
theorem contour_local_evolution_unique {first second : ℝ → PeriodicC1HolderHalf}
    {lower upper initialTime radius : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (initial_mem : initialTime ∈ Ioo lower upper)
    (first_equation : ∀ time ∈ Ioo lower upper,
      HasDerivAt first (extendedContourVelocity (first time)) time)
    (second_equation : ∀ time ∈ Ioo lower upper,
      HasDerivAt second (extendedContourVelocity (second time)) time)
    (first_near : ∀ time ∈ Ioo lower upper, ‖first time - standardCircleBanach‖ ≤ radius)
    (second_near : ∀ time ∈ Ioo lower upper, ‖second time - standardCircleBanach‖ ≤ radius)
    (initial_eq : first initialTime = second initialTime) :
    EqOn first second (Ioo lower upper) := by
  exact ODE_solution_unique_of_mem_Ioo
    (v := fun _ => extendedContourVelocity)
    (s := fun _ => closedBall standardCircleBanach radius)
    (fun _ _ => extendedContourVelocity_lipschitzOn radius_nonneg radius_small)
    initial_mem
    (fun time time_mem => ⟨first_equation time time_mem, by
      change dist (first time) standardCircleBanach ≤ radius
      rw [dist_eq_norm (first time) standardCircleBanach]
      exact first_near time time_mem⟩)
    (fun time time_mem => ⟨second_equation time time_mem, by
      change dist (second time) standardCircleBanach ≤ radius
      rw [dist_eq_norm (second time) standardCircleBanach]
      exact second_near time time_mem⟩)
    initial_eq

end

end EulerNonuniqueness.Paper
