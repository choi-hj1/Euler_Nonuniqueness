import EulerNonuniqueness.Section3.MovingContourCutoffMargin
import EulerNonuniqueness.General.FinitePositiveMargin

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingInitialMarginHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingInitialMarginC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

def FiniteContourConfiguration.movingCircleInitialState {count : ℕ}
    (configuration : FiniteContourConfiguration count) : MovingContourState count :=
  (0, configuration.center, fun _ => standardCircleBanach)

theorem FiniteContourConfiguration.exists_movingCircleInitialState_margin {count : ℕ}
    (configuration : FiniteContourConfiguration count) (countPositive : 0 < count)
    {shapeRadius : ℝ} (shapePositive : 0 < shapeRadius) :
    ∃ centerBound ≥ 0, ∃ gap > 0, ∃ margin > 0,
      configuration.movingCircleInitialState ∈ configuration.movingStateAdmissible centerBound shapeRadius gap ∧
      2 * margin ≤ infDist configuration.movingCircleInitialState
        (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ := by
  classical
  let separationGap : Fin count × Fin count → ℝ := fun indices =>
    if indices.1 = indices.2 then 1 else
      ‖configuration.center indices.1 - configuration.center indices.2‖ -
        3 * (configuration.radius indices.1 + configuration.radius indices.2)
  have positiveGap : ∀ indices, 0 < separationGap indices := by
    intro indices
    dsimp only [separationGap]
    split_ifs with equal
    · norm_num
    · exact sub_pos.mpr (configuration.separated indices.1 indices.2 equal)
  obtain ⟨minimumGap, minimumPositive, gapBound⟩ :=
    EulerNonuniqueness.General.exists_positive_uniform_lower_bound_finite separationGap positiveGap
  let centerBound : ℝ := (∑ index, ‖configuration.center index‖) + 1
  let gap : ℝ := minimumGap / 2
  let margin : ℝ := min (min (shapeRadius / 4) (minimumGap / 16)) (1 / 4)
  have centerNonnegative : 0 ≤ centerBound := by
    dsimp only [centerBound]
    positivity
  have gapPositive : 0 < gap := by dsimp only [gap]; positivity
  have marginPositive : 0 < margin := by
    dsimp only [margin]
    exact lt_min (lt_min (by positivity) (by positivity)) (by norm_num)
  have marginShape : margin ≤ shapeRadius / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have marginGap : margin ≤ minimumGap / 16 := (min_le_left _ _).trans (min_le_right _ _)
  have marginOne : margin ≤ 1 / 4 := min_le_right _ _
  have centersInside : ∀ index, ‖configuration.movingCircleInitialState.2.1 index‖ + 2 * margin ≤ centerBound := by
    intro index
    have sumBound : ‖configuration.center index‖ ≤ ∑ other, ‖configuration.center other‖ :=
      Finset.single_le_sum (fun other _ => norm_nonneg (configuration.center other)) (Finset.mem_univ index)
    change ‖configuration.center index‖ + 2 * margin ≤ centerBound
    dsimp only [centerBound]
    linarith
  have shapesInside : ∀ index, ‖configuration.movingCircleInitialState.2.2 index - standardCircleBanach‖ + 2 * margin ≤ shapeRadius := by
    intro index
    change ‖standardCircleBanach - standardCircleBanach‖ + 2 * margin ≤ shapeRadius
    rw [sub_self (standardCircleBanach : PeriodicC1HolderHalf), norm_zero (E := PeriodicC1HolderHalf), zero_add]
    linarith
  have separated : ∀ first second, first ≠ second →
      3 * (configuration.radius first + configuration.radius second) + gap + 2 * (2 * margin) ≤
        ‖configuration.movingCircleInitialState.2.1 first - configuration.movingCircleInitialState.2.1 second‖ := by
    intro first second different
    have actualGap := gapBound (first, second)
    dsimp only [separationGap] at actualGap
    rw [if_neg different] at actualGap
    change 3 * (configuration.radius first + configuration.radius second) + gap + 2 * (2 * margin) ≤
      ‖configuration.center first - configuration.center second‖
    dsimp only [gap]
    linarith
  have lowerBound := configuration.movingStateAdmissible_infDist_lower_bound countPositive centerNonnegative
    configuration.movingCircleInitialState centersInside shapesInside separated
  refine ⟨centerBound, centerNonnegative, gap, gapPositive, margin, marginPositive, ?_, lowerBound⟩
  have ballInside := configuration.ball_subset_movingStateAdmissible_of_margin
    configuration.movingCircleInitialState centersInside shapesInside separated
  apply ballInside
  simpa only [mem_ball, dist_self] using (show 0 < 2 * margin by positivity)

end EulerNonuniqueness.Paper
