import EulerNonuniqueness.Section6.PaperShapeBranch

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem paper_shape_eq_coherent_chart_on_small_interval {count : ℕ} (motion : PatchMotion count)
    (index : Fin count) {horizon : ℝ}
    (positiveContinuous : ContinuousOn (fun time => positiveHalfDiagonal motion time index) (Icc 0 horizon))
    (negativeContinuous : ContinuousOn (fun time => negativeHalfDiagonal motion time index) (Icc 0 horizon))
    (positiveNonzero : ∀ time ∈ Icc 0 horizon, positiveHalfDiagonal motion time index ≠ 0)
    (negativeNonzero : ∀ time ∈ Icc 0 horizon, negativeHalfDiagonal motion time index ≠ 0)
    (initialUpper : 0 < (negativeHalfDiagonal motion 0 index / positiveHalfDiagonal motion 0 index).im)
    (small : ∀ time ∈ Icc 0 horizon,
      |(Section6.pointShapeChart (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)).1| +
        |(Section6.pointShapeChart (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)).2| ≤ 1 / 4) :
    ∀ time ∈ Icc 0 horizon,
      Section6.pointShapeChart (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index) =
        (unstableShape motion time index, stableShape motion time index) := by
  exact paper_shape_eq_coherent_chart_on_interval motion index positiveContinuous negativeContinuous positiveNonzero
    initialUpper (fun time member => Section6.pointShapeChart_leftHalfPlane_of_small
      (positiveNonzero time member) (negativeNonzero time member) (small time member))

end EulerNonuniqueness.Paper
