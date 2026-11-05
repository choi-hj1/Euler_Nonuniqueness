import EulerNonuniqueness.Section6.PaperStraightenedShapeDynamics

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_referenceStraightenedShape_difference_small
    {graph coordinate : ℝ → ℝ}
    (graphContinuous : ContinuousAt graph 0) (coordinateContinuous : ContinuousAt coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    {tolerance : ℝ} (tolerancePositive : 0 < tolerance) :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
      ∀ {count : ℕ} (first second : PatchMotion count) (index : Fin count) (time : ℝ),
        |unstableShape first time index| + |stableShape first time index| ≤ radius →
        |unstableShape second time index| + |stableShape second time index| ≤ radius →
        |(referenceStraightenedShape first graph coordinate index time -
            referenceStraightenedShape second graph coordinate index time).1| +
          |(referenceStraightenedShape first graph coordinate index time -
            referenceStraightenedShape second graph coordinate index time).2| ≤ tolerance := by
  have chartContinuous : ContinuousAt (localNormalFormChart graph coordinate) (0 : ℝ × ℝ) :=
    (coordinateContinuous.comp (f := Prod.fst) (x := (0 : ℝ × ℝ)) continuousAt_fst).prodMk
      (continuousAt_snd.sub (graphContinuous.comp (f := Prod.fst) (x := (0 : ℝ × ℝ)) continuousAt_fst))
  have sizeContinuous := chartContinuous.fst.abs.add chartContinuous.snd.abs
  have zeroSmall : |(localNormalFormChart graph coordinate (0 : ℝ × ℝ)).1| +
      |(localNormalFormChart graph coordinate (0 : ℝ × ℝ)).2| < tolerance / 2 := by
    simp only [localNormalFormChart, Prod.fst_zero, Prod.snd_zero, graphZero, coordinateZero, sub_zero,
      abs_zero, zero_add]
    positivity
  obtain ⟨ambientRadius, ambientPositive, inside⟩ := Metric.mem_nhds_iff.mp
    (sizeContinuous.eventually (eventually_lt_nhds zeroSmall))
  let radius := min (ambientRadius / 2) (1 / 4 : ℝ)
  have radiusPositive : 0 < radius := lt_min (half_pos ambientPositive) (by norm_num)
  have radiusBelow : radius < ambientRadius :=
    (min_le_left _ _).trans_lt (half_lt_self ambientPositive)
  have small (point : ℝ × ℝ) (physicalSmall : |point.1| + |point.2| ≤ radius) :
      |(localNormalFormChart graph coordinate point).1| +
        |(localNormalFormChart graph coordinate point).2| < tolerance / 2 := by
    apply inside
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (max_le (le_add_of_nonneg_right (abs_nonneg _))
      (le_add_of_nonneg_left (abs_nonneg _))).trans_lt (physicalSmall.trans_lt radiusBelow)
  refine ⟨radius, radiusPositive, min_le_right _ _, ?_⟩
  intro count first second index time firstSmall secondSmall
  have firstBound := small (unstableShape first time index, stableShape first time index) firstSmall
  have secondBound := small (unstableShape second time index, stableShape second time index) secondSmall
  change |(referenceStraightenedShape first graph coordinate index time).1| +
    |(referenceStraightenedShape first graph coordinate index time).2| < tolerance / 2 at firstBound
  change |(referenceStraightenedShape second graph coordinate index time).1| +
    |(referenceStraightenedShape second graph coordinate index time).2| < tolerance / 2 at secondBound
  have firstTriangle := norm_sub_le (referenceStraightenedShape first graph coordinate index time).1
    (referenceStraightenedShape second graph coordinate index time).1
  have secondTriangle := norm_sub_le (referenceStraightenedShape first graph coordinate index time).2
    (referenceStraightenedShape second graph coordinate index time).2
  simp only [Real.norm_eq_abs] at firstTriangle secondTriangle
  change |(referenceStraightenedShape first graph coordinate index time).1 -
      (referenceStraightenedShape second graph coordinate index time).1| +
    |(referenceStraightenedShape first graph coordinate index time).2 -
      (referenceStraightenedShape second graph coordinate index time).2| ≤ tolerance
  linarith only [firstTriangle, secondTriangle, firstBound, secondBound]

end EulerNonuniqueness.Paper
