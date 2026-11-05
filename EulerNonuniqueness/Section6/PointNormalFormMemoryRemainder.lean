import EulerNonuniqueness.Section6.NormalFormRelativeCoordinates

noncomputable section

namespace EulerNonuniqueness.Section6

theorem graded_saddle_difference_budget (firstUnstable firstStable secondUnstable secondStable : ℝ) :
    (|firstStable| + |secondStable|) * |firstUnstable - secondUnstable| +
      (|firstUnstable| + |secondUnstable| + |firstStable| + |secondStable|) * |firstStable - secondStable| ≤
    2 * (|firstUnstable - secondUnstable| + |firstStable - secondStable|) *
      (|firstStable - secondStable| + |secondUnstable| + |secondStable|) := by
  have unstableTriangle : |firstUnstable| ≤ |firstUnstable - secondUnstable| + |secondUnstable| := by
    simpa only [sub_add_cancel] using abs_add (firstUnstable - secondUnstable) secondUnstable
  have stableTriangle : |firstStable| ≤ |firstStable - secondStable| + |secondStable| := by
    simpa only [sub_add_cancel] using abs_add (firstStable - secondStable) secondStable
  have firstTerm := mul_le_mul_of_nonneg_right (add_le_add_right stableTriangle |secondStable|) (abs_nonneg (firstUnstable - secondUnstable))
  have secondTerm := mul_le_mul_of_nonneg_right
    (add_le_add (add_le_add_right unstableTriangle |secondUnstable|) (add_le_add_right stableTriangle |secondStable|))
    (abs_nonneg (firstStable - secondStable))
  have extra : 0 ≤ 2 * |firstUnstable - secondUnstable| * |secondUnstable| + |firstStable - secondStable| ^ 2 := by positivity
  nlinarith only [firstTerm, secondTerm, extra]

theorem exists_uniform_pointNormalForm_memory_remainder :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ constant ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ frequency : ℝ, ∀ first second : ℝ × ℝ,
      |first.1| + |first.2| < radius → |second.1| + |second.2| < radius →
      let firstChart := localNormalFormChart graph coordinate first
      let secondChart := localNormalFormChart graph coordinate second
      ‖localNormalFormError frequency graph coordinate first - localNormalFormError frequency graph coordinate second‖ ≤
        constant * |frequency| * (|firstChart.1 - secondChart.1| + |firstChart.2 - secondChart.2|) *
          (|firstChart.2 - secondChart.2| + |secondChart.1| + |secondChart.2|) := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    constant, constantNonnegative, radius, radiusPositive, bound⟩ := exists_uniform_localNormalForm_relative_coordinates
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero, coordinateDerivative,
    2 * constant, by positivity, radius, radiusPositive, ?_⟩
  intro frequency first second firstSmall secondSmall
  dsimp only
  apply (bound frequency first second firstSmall secondSmall).trans
  have actual := mul_le_mul_of_nonneg_left
    (graded_saddle_difference_budget (localNormalFormChart graph coordinate first).1 (localNormalFormChart graph coordinate first).2
      (localNormalFormChart graph coordinate second).1 (localNormalFormChart graph coordinate second).2)
    (mul_nonneg constantNonnegative (abs_nonneg frequency))
  convert actual using 1 <;> ring

end EulerNonuniqueness.Section6
