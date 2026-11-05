import EulerNonuniqueness.Section3.MovingContourInitialMargin
import Mathlib.Topology.Order.Compact

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingCompactMarginHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingCompactMarginC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem FiniteContourConfiguration.exists_compact_circle_initial_margin
    {Parameter : Type*} [TopologicalSpace Parameter] [CompactSpace Parameter]
    {count : ℕ} (configuration : FiniteContourConfiguration count) (countPositive : 0 < count)
    (centers : Parameter → Fin count → ℂ) (centersContinuous : Continuous centers)
    (separation : ∀ parameter first second, first ≠ second →
      3 * (configuration.radius first + configuration.radius second) < ‖centers parameter first - centers parameter second‖)
    {shapeRadius : ℝ} (shapePositive : 0 < shapeRadius) :
    ∃ centerBound ≥ 0, ∃ gap > 0, ∃ margin > 0, ∀ parameter,
      (0, centers parameter, fun _ => standardCircleBanach) ∈ configuration.movingStateAdmissible centerBound shapeRadius gap ∧
      2 * margin ≤ infDist (0, centers parameter, fun _ => standardCircleBanach)
        (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ := by
  classical
  let separationGap : (Fin count × Fin count) → Parameter → ℝ := fun indices parameter =>
    if indices.1 = indices.2 then 1 else ‖centers parameter indices.1 - centers parameter indices.2‖ -
      3 * (configuration.radius indices.1 + configuration.radius indices.2)
  have uniformPairGap : ∀ indices, ∃ lower > 0, ∀ parameter, lower ≤ separationGap indices parameter := by
    intro indices
    have gapContinuous : Continuous (separationGap indices) := by
      dsimp only [separationGap]
      split_ifs
      · exact continuous_const
      · exact (((continuous_apply indices.1).comp centersContinuous).sub
          ((continuous_apply indices.2).comp centersContinuous)).norm.sub continuous_const
    obtain ⟨lower, positive, bound⟩ := isCompact_univ.exists_forall_le' gapContinuous.continuousOn
      (show ∀ parameter ∈ (univ : Set Parameter), 0 < separationGap indices parameter by
        intro parameter _member
        dsimp only [separationGap]
        split_ifs with equal
        · norm_num
        · exact sub_pos.mpr (separation parameter indices.1 indices.2 equal))
    exact ⟨lower, positive, fun parameter => bound parameter (mem_univ _)⟩
  choose pairGap pairPositive pairLower using uniformPairGap
  obtain ⟨minimumGap, minimumPositive, gapBound⟩ :=
    EulerNonuniqueness.General.exists_positive_uniform_lower_bound_finite pairGap pairPositive
  obtain ⟨centerRadius, centerPositive, centerNormBound⟩ :=
    (isCompact_univ.image centersContinuous).isBounded.exists_pos_norm_le
  let centerBound : ℝ := centerRadius + 1
  let gap : ℝ := minimumGap / 2
  let margin : ℝ := min (min (shapeRadius / 4) (minimumGap / 16)) (1 / 4)
  have centerNonnegative : 0 ≤ centerBound := by dsimp only [centerBound]; positivity
  have gapPositive : 0 < gap := by dsimp only [gap]; positivity
  have marginPositive : 0 < margin := lt_min (lt_min (by positivity) (by positivity)) (by norm_num)
  have marginShape : margin ≤ shapeRadius / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have marginGap : margin ≤ minimumGap / 16 := (min_le_left _ _).trans (min_le_right _ _)
  have marginOne : margin ≤ 1 / 4 := min_le_right _ _
  refine ⟨centerBound, centerNonnegative, gap, gapPositive, margin, marginPositive, ?_⟩
  intro parameter
  let initial : MovingContourState count := (0, centers parameter, fun _ => standardCircleBanach)
  have centersInside : ∀ index, ‖initial.2.1 index‖ + 2 * margin ≤ centerBound := by
    intro index
    have bound := (norm_le_pi_norm (centers parameter) index).trans
      (centerNormBound (centers parameter) (mem_image_of_mem centers (mem_univ parameter)))
    change ‖centers parameter index‖ + 2 * margin ≤ centerBound
    dsimp only [centerBound]
    linarith
  have shapesInside : ∀ index, ‖initial.2.2 index - standardCircleBanach‖ + 2 * margin ≤ shapeRadius := by
    intro index
    change ‖standardCircleBanach - standardCircleBanach‖ + 2 * margin ≤ shapeRadius
    rw [sub_self (standardCircleBanach : PeriodicC1HolderHalf), norm_zero (E := PeriodicC1HolderHalf), zero_add]
    linarith
  have separated : ∀ first second, first ≠ second →
      3 * (configuration.radius first + configuration.radius second) + gap + 2 * (2 * margin) ≤
        ‖initial.2.1 first - initial.2.1 second‖ := by
    intro first second different
    have actualGap := (gapBound (first, second)).trans (pairLower (first, second) parameter)
    dsimp only [separationGap] at actualGap
    rw [if_neg different] at actualGap
    change 3 * (configuration.radius first + configuration.radius second) + gap + 2 * (2 * margin) ≤
      ‖centers parameter first - centers parameter second‖
    dsimp only [gap]
    linarith
  have lowerBound := configuration.movingStateAdmissible_infDist_lower_bound countPositive centerNonnegative
    initial centersInside shapesInside separated
  refine ⟨?_, lowerBound⟩
  apply configuration.ball_subset_movingStateAdmissible_of_margin initial centersInside shapesInside separated
  change dist initial initial < 2 * margin
  rw [dist_self]
  positivity

end EulerNonuniqueness.Paper
