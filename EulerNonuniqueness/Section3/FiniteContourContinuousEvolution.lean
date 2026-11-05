import EulerNonuniqueness.Section3.BanachContinuousLocalEvolution
import EulerNonuniqueness.Section3.FiniteContourField

open Set Metric

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

local instance finiteContinuousHolderNormedSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance finiteContinuousC1NormedSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem finite_contour_continuous_local_evolution {count : ℕ}
    (configuration : FiniteContourConfiguration count) :
    ∃ duration > (0 : ℝ), ∃ solution : ℝ → Fin count → PeriodicC1HolderHalf,
      solution 0 = standardContours count ∧ Continuous solution ∧
      Continuous (configuration.vectorField ∘ solution) ∧
      (∀ time index, ‖solution time index - standardCircleBanach‖ < min (1 / 3) (2 / (3 * Real.pi))) ∧
      (∀ time index, ‖solution time index‖ ≤ 3) ∧
      ∀ time ∈ Ioo (-duration) duration,
        HasDerivAt solution (configuration.vectorField (solution time)) time := by
  let margin := min (1 / 3 : ℝ) (2 / (3 * Real.pi))
  let radius := margin / 2
  have margin_positive : 0 < margin := by dsimp [margin]; positivity
  have radius_positive : 0 < radius := by dsimp [radius]; positivity
  have radius_margin : radius < margin := by dsimp only [radius]; linarith
  have margin_safe : margin ≤ min 1 (2 / (3 * Real.pi)) := by
    exact le_min ((min_le_left _ _).trans (by norm_num)) (min_le_right _ _)
  have radius_safe : radius < min 1 (2 / (3 * Real.pi)) := radius_margin.trans_le margin_safe
  let constant : NNReal := ⟨configuration.lipschitzConstant radius,
    configuration.lipschitzConstant_nonneg radius_positive.le radius_safe⟩
  obtain ⟨duration, duration_positive, solution, initial_eq, continuous, velocity_continuous, stays, equation⟩ :=
    banach_continuous_local_evolution_of_lipschitzOn_ball configuration.vectorField (standardContours count)
      radius_positive constant (configuration.vectorField_lipschitzOn_ball radius_positive.le radius_safe)
  have nearby : ∀ time, ‖solution time - standardContours count‖ ≤ radius := fun time =>
    (dist_eq_norm (solution time) (standardContours count)) ▸ stays time
  exact ⟨duration, duration_positive, solution, initial_eq, continuous, velocity_continuous,
    fun time index => (near_standardContours_component (solution time) (nearby time) index).trans_lt radius_margin,
    fun time => near_standardContours_norm_bound (solution time) (nearby time) radius_safe, equation⟩

end

end EulerNonuniqueness.Paper
