import EulerNonuniqueness.Section6.UpperShapeBranch
import EulerNonuniqueness.Section4.ReferenceStatement

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem pointShapeChart_eq_paper_shape_of_upper {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count)
    (upper : 0 < (negativeHalfDiagonal motion time index / positiveHalfDiagonal motion time index).im) :
    Section6.pointShapeChart (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index) =
      (unstableShape motion time index, stableShape motion time index) := by
  rw [Section6.pointShapeChart, Section6.pointShapeAngle_eq_twice_arg_of_upper upper]
  simp only [Section6.shapeChart, Section6.pointShapeRatio, unstableShape, stableShape, radialShape, angularShape]
  rw [div_sub_one Section2.rhombusRatio_pos.ne']
  rfl

theorem paper_shape_eq_coherent_chart_on_interval {count : ℕ} (motion : PatchMotion count)
    (index : Fin count) {horizon : ℝ}
    (positiveContinuous : ContinuousOn (fun time => positiveHalfDiagonal motion time index) (Icc 0 horizon))
    (negativeContinuous : ContinuousOn (fun time => negativeHalfDiagonal motion time index) (Icc 0 horizon))
    (positiveNonzero : ∀ time ∈ Icc 0 horizon, positiveHalfDiagonal motion time index ≠ 0)
    (initialUpper : 0 < (negativeHalfDiagonal motion 0 index / positiveHalfDiagonal motion 0 index).im)
    (left : ∀ time ∈ Icc 0 horizon,
      ((negativeHalfDiagonal motion time index / positiveHalfDiagonal motion time index) ^ 2).re < 0) :
    ∀ time ∈ Icc 0 horizon,
      Section6.pointShapeChart (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index) =
        (unstableShape motion time index, stableShape motion time index) := by
  have continuous := negativeContinuous.div positiveContinuous positiveNonzero
  have upper := Section6.upperHalfPlane_of_initial_and_square_left continuous initialUpper left
  intro time member
  exact pointShapeChart_eq_paper_shape_of_upper motion time index (upper time member)

end EulerNonuniqueness.Paper
