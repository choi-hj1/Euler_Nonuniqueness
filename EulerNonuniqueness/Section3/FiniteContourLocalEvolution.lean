import EulerNonuniqueness.Section3.FiniteContourField

open Set Metric

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 500000

local instance finiteEvolutionHolderNormedSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance finiteEvolutionC1NormedSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

set_option maxHeartbeats 1000000 in
theorem finite_contour_local_evolution {count : ℕ} (configuration : FiniteContourConfiguration count) :
    ∃ duration > (0 : ℝ), ∃ solution : ℝ → Fin count → PeriodicC1HolderHalf,
      solution 0 = standardContours count ∧
      (∀ time index, ‖solution time index - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) ∧
      (∀ time index, ‖solution time index‖ ≤ 3) ∧
      ∀ time ∈ Ioo (-duration) duration,
        HasDerivAt solution (configuration.vectorField (solution time)) time := by
  let radius := min 1 (2 / (3 * Real.pi)) / 2
  have safe_pos : 0 < min (1 : ℝ) (2 / (3 * Real.pi)) := by positivity
  have radius_pos : 0 < radius := by dsimp only [radius]; positivity
  have radius_small : radius < min 1 (2 / (3 * Real.pi)) := by dsimp only [radius]; linarith
  let constant : NNReal := ⟨configuration.lipschitzConstant radius,
    configuration.lipschitzConstant_nonneg radius_pos.le radius_small⟩
  obtain ⟨duration, duration_pos, solution, initial_eq, stays, equation⟩ :=
    banach_local_evolution_of_lipschitzOn_ball configuration.vectorField (standardContours count)
      radius_pos constant (configuration.vectorField_lipschitzOn_ball radius_pos.le radius_small)
  have nearby : ∀ time, ‖solution time - standardContours count‖ ≤ radius := fun time =>
    (dist_eq_norm (solution time) (standardContours count)) ▸ stays time
  exact ⟨duration, duration_pos, solution, initial_eq,
    fun time index => (near_standardContours_component (solution time) (nearby time) index).trans_lt radius_small,
    fun time => near_standardContours_norm_bound (solution time) (nearby time) radius_small, equation⟩

def finiteContourLabelEvaluation {count : ℕ} (index : Fin count) (label : ℝ) :
    (Fin count → PeriodicC1HolderHalf) →L[ℝ] ℂ := by
  let evaluation : (Fin count → PeriodicC1HolderHalf) →ₗ[ℝ] ℂ := {
    toFun := fun data => (data index).val.1 label
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  exact LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Fin count → PeriodicC1HolderHalf) (F := ℂ)
    evaluation 1 (fun data => by
      change ‖(data index).val.1 label‖ ≤ 1 * ‖data‖
      rw [one_mul]
      exact (PeriodicC1HolderHalf.value_bound (data index) label).trans (norm_le_pi_norm data index))

set_option maxHeartbeats 1000000 in
theorem finite_contour_local_label_evolution {count : ℕ} (configuration : FiniteContourConfiguration count) :
    ∃ duration > (0 : ℝ), ∃ solution : ℝ → Fin count → PeriodicC1HolderHalf,
      solution 0 = standardContours count ∧
      (∀ time index, ‖solution time index - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) ∧
      (∀ time index, ‖solution time index‖ ≤ 3) ∧
      ∀ time ∈ Ioo (-duration) duration, ∀ index label,
        HasDerivAt (fun time => (solution time index).val.1 label)
          ((configuration.vectorField (solution time) index).val.1 label) time := by
  obtain ⟨duration, duration_pos, solution, initial_eq, nearby, bounded, equation⟩ :=
    finite_contour_local_evolution configuration
  refine ⟨duration, duration_pos, solution, initial_eq, nearby, bounded, ?_⟩
  intro time time_mem index label
  exact ((finiteContourLabelEvaluation index label).hasFDerivAt (x := solution time)).comp_hasDerivAt time
    (equation time time_mem)

end

end EulerNonuniqueness.Paper
