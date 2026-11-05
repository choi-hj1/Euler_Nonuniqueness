import EulerNonuniqueness.Section3.MovingCentroidGaugeExistence

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingCutoffMarginHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingCutoffMarginC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem FiniteContourConfiguration.movingStateAdmissible_compl_nonempty {count : ℕ}
    (configuration : FiniteContourConfiguration count) (countPositive : 0 < count)
    {centerBound : ℝ} (nonnegative : 0 ≤ centerBound) (shapeRadius gap : ℝ) :
    (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ.Nonempty := by
  let state : MovingContourState count := (0, (fun _ => ((centerBound + 1 : ℝ) : ℂ)), fun _ => standardCircleBanach)
  refine ⟨state, ?_⟩
  intro inside
  have bound := inside.1 ⟨0, countPositive⟩
  change ‖((centerBound + 1 : ℝ) : ℂ)‖ ≤ centerBound at bound
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at bound
  linarith

theorem FiniteContourConfiguration.ball_subset_movingStateAdmissible_of_margin {count : ℕ}
    (configuration : FiniteContourConfiguration count) {centerBound shapeRadius gap margin : ℝ}
    (state : MovingContourState count)
    (centersInside : ∀ index, ‖state.2.1 index‖ + margin ≤ centerBound)
    (shapesInside : ∀ index, ‖state.2.2 index - standardCircleBanach‖ + margin ≤ shapeRadius)
    (separated : ∀ first second, first ≠ second → 3 * (configuration.radius first + configuration.radius second) +
      gap + 2 * margin ≤ ‖state.2.1 first - state.2.1 second‖) :
    ball state margin ⊆ configuration.movingStateAdmissible centerBound shapeRadius gap := by
  intro nearby member
  have distance : ‖nearby - state‖ < margin := by
    rw [mem_ball, dist_eq_norm nearby state] at member
    exact member
  refine ⟨?_, ?_, ?_⟩
  · intro index
    have difference := (movingContourState_center_norm_sub_le nearby state index).trans_lt distance
    have triangle : ‖nearby.2.1 index‖ ≤ ‖nearby.2.1 index - state.2.1 index‖ + ‖state.2.1 index‖ := by
      calc
        _ = ‖(nearby.2.1 index - state.2.1 index) + state.2.1 index‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    linarith [centersInside index]
  · intro index
    have difference := (movingContourState_shape_norm_sub_le nearby state index).trans_lt distance
    have triangle := dist_triangle (nearby.2.2 index) (state.2.2 index) standardCircleBanach
    rw [dist_eq_norm (nearby.2.2 index) standardCircleBanach,
      dist_eq_norm (nearby.2.2 index) (state.2.2 index), dist_eq_norm (state.2.2 index) standardCircleBanach] at triangle
    linarith [shapesInside index]
  · intro first second distinct
    have firstDifference := (movingContourState_center_norm_sub_le nearby state first).trans_lt distance
    have secondDifference := (movingContourState_center_norm_sub_le nearby state second).trans_lt distance
    have triangle : ‖state.2.1 first - state.2.1 second‖ ≤ ‖nearby.2.1 first - state.2.1 first‖ +
        ‖nearby.2.1 first - nearby.2.1 second‖ + ‖nearby.2.1 second - state.2.1 second‖ := by
      have identity : state.2.1 first - state.2.1 second =
          -(nearby.2.1 first - state.2.1 first) + (nearby.2.1 first - nearby.2.1 second) +
            (nearby.2.1 second - state.2.1 second) := by ring
      rw [identity]
      exact (norm_add_le _ _).trans (add_le_add_right ((norm_add_le _ _).trans_eq (by rw [norm_neg])) _)
    linarith [separated first second distinct]

theorem FiniteContourConfiguration.movingStateAdmissible_infDist_lower_bound {count : ℕ}
    (configuration : FiniteContourConfiguration count) (countPositive : 0 < count)
    {centerBound shapeRadius gap margin : ℝ} (centerNonnegative : 0 ≤ centerBound)
    (state : MovingContourState count)
    (centersInside : ∀ index, ‖state.2.1 index‖ + margin ≤ centerBound)
    (shapesInside : ∀ index, ‖state.2.2 index - standardCircleBanach‖ + margin ≤ shapeRadius)
    (separated : ∀ first second, first ≠ second → 3 * (configuration.radius first + configuration.radius second) +
      gap + 2 * margin ≤ ‖state.2.1 first - state.2.1 second‖) :
    margin ≤ infDist state (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ := by
  apply (le_infDist (configuration.movingStateAdmissible_compl_nonempty countPositive centerNonnegative shapeRadius gap)).mpr
  intro nearby outside
  by_contra notFar
  have close : nearby ∈ ball state margin := by
    rw [mem_ball, dist_comm]
    exact lt_of_not_ge notFar
  exact outside (configuration.ball_subset_movingStateAdmissible_of_margin state centersInside shapesInside separated close)

theorem FiniteContourConfiguration.movingState_cutoff_eq_one_of_margin {count : ℕ}
    (configuration : FiniteContourConfiguration count) (countPositive : 0 < count)
    {centerBound shapeRadius gap margin : ℝ} (centerNonnegative : 0 ≤ centerBound) (marginPositive : 0 < margin)
    (state : MovingContourState count)
    (centersInside : ∀ index, ‖state.2.1 index‖ + margin ≤ centerBound)
    (shapesInside : ∀ index, ‖state.2.2 index - standardCircleBanach‖ + margin ≤ shapeRadius)
    (separated : ∀ first second, first ≠ second → 3 * (configuration.radius first + configuration.radius second) +
      gap + 2 * margin ≤ ‖state.2.1 first - state.2.1 second‖) :
    EulerNonuniqueness.General.distanceFieldCutoff
      (configuration.movingStateAdmissible centerBound shapeRadius gap) margin state = 1 :=
  EulerNonuniqueness.General.distanceFieldCutoff_one _ marginPositive state
    (configuration.movingStateAdmissible_infDist_lower_bound countPositive centerNonnegative state centersInside shapesInside separated)

end EulerNonuniqueness.Paper
