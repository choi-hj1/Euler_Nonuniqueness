import EulerNonuniqueness.Section3.PhasedContourField
import EulerNonuniqueness.Section3.BanachContinuousLocalEvolution

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance phasedLocalEvolutionHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph

local instance phasedLocalEvolutionC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem finite_phased_contour_continuous_local_evolution {count : ℕ}
    (configuration : FiniteContourConfiguration count) (phase : Fin count → Circle)
    (initial : Fin count → PeriodicC1HolderHalf)
    (initial_nearby : ‖initial - standardContours count‖ < min (1 / 3) (2 / (3 * Real.pi))) :
    ∃ duration > (0 : ℝ), ∃ solution : ℝ → Fin count → PeriodicC1HolderHalf,
      solution 0 = initial ∧ Continuous solution ∧
      Continuous (configuration.phasedVectorField phase ∘ solution) ∧
      (∀ time index, ‖solution time index - standardCircleBanach‖ < min (1 / 3) (2 / (3 * Real.pi))) ∧
      (∀ time index, ‖solution time index‖ ≤ 3) ∧
      ∀ time ∈ Ioo (-duration) duration,
        HasDerivAt solution (configuration.phasedVectorField phase (solution time)) time := by
  let margin := min (1 / 3 : ℝ) (2 / (3 * Real.pi))
  let initialDistance := ‖initial - standardContours count‖
  let outerRadius := (margin + initialDistance) / 2
  let radius := (margin - initialDistance) / 4
  have initial_lt : initialDistance < margin := initial_nearby
  have margin_positive : 0 < margin := by dsimp [margin]; positivity
  have radius_positive : 0 < radius := by dsimp only [radius]; linarith
  have outer_positive : 0 < outerRadius := by
    dsimp only [outerRadius]
    linarith [norm_nonneg (initial - standardContours count)]
  have outer_margin : outerRadius < margin := by dsimp only [outerRadius]; linarith
  have outer_safe : outerRadius < min 1 (2 / (3 * Real.pi)) := by
    apply outer_margin.trans_le
    exact le_min ((min_le_left _ _).trans (by norm_num)) (min_le_right _ _)
  have ball_inside : closedBall initial radius ⊆ closedBall (standardContours count) outerRadius := by
    intro data membership
    have close : ‖data - initial‖ ≤ radius := (dist_eq_norm data initial) ▸ membership
    have triangle : ‖data - standardContours count‖ ≤ ‖data - initial‖ + initialDistance := by
      dsimp only [initialDistance]
      have identity : data - standardContours count = (data - initial) + (initial - standardContours count) := by abel
      rw [identity]
      exact norm_add_le (data - initial) (initial - standardContours count)
    have radius_bound : radius + initialDistance ≤ outerRadius := by
      dsimp only [radius, outerRadius]
      linarith
    have near : ‖data - standardContours count‖ ≤ outerRadius :=
      triangle.trans ((add_le_add_right close initialDistance).trans radius_bound)
    change dist data (standardContours count) ≤ outerRadius
    rw [dist_eq_norm data (standardContours count)]
    exact near
  let constant : NNReal := ⟨configuration.lipschitzConstant outerRadius,
    configuration.lipschitzConstant_nonneg outer_positive.le outer_safe⟩
  have local_lipschitz : LipschitzOnWith constant (configuration.phasedVectorField phase) (closedBall initial radius) :=
    (configuration.phasedVectorField_lipschitzOn_ball phase outer_positive.le outer_safe).mono ball_inside
  obtain ⟨duration, duration_positive, solution, initial_eq, continuous, velocity_continuous, stays, equation⟩ :=
    banach_continuous_local_evolution_of_lipschitzOn_ball (configuration.phasedVectorField phase) initial
      radius_positive constant local_lipschitz
  have nearby : ∀ time, ‖solution time - standardContours count‖ ≤ outerRadius := by
    intro time
    exact (dist_eq_norm (solution time) (standardContours count)) ▸ ball_inside (stays time)
  refine ⟨duration, duration_positive, solution, initial_eq, continuous, velocity_continuous, ?_, ?_, equation⟩
  · intro time index
    exact (near_standardContours_component (solution time) (nearby time) index).trans_lt outer_margin
  · intro time
    exact near_standardContours_norm_bound (solution time) (nearby time) outer_safe

end EulerNonuniqueness.Paper
