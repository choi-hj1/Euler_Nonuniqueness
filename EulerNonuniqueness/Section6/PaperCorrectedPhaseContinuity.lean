import EulerNonuniqueness.Section4.PaperShapeContinuity
import EulerNonuniqueness.Section6.PaperCorrectedPhaseDynamics

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem correctedPaperPhase_continuousOn_of_centroids
    {count : ℕ} (motion : PatchMotion count) (correction phase : ℝ → ℝ) (index : Fin count) {times : Set ℝ}
    (positions : ∀ patch : Fin 4, ContinuousOn (fun time => patchCentroid motion time index patch) times)
    (phaseContinuous : ContinuousOn phase times)
    (small : ∀ time ∈ times, |unstableShape motion time index| + |stableShape motion time index| ≤ 1 / 4)
    (correctionContinuous : ∀ time ∈ times, ContinuousAt correction (unstableShape motion time index)) :
    ContinuousOn (correctedPaperPhase correction phase motion index) times := by
  have shape := paper_shape_continuousOn_of_centroids motion index positions small
  have composition : ContinuousOn (fun time => correction (unstableShape motion time index)) times := by
    intro time inside
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun current : ℝ => unstableShape motion current index) (correctionContinuous time inside) (shape.fst time inside)
  have angle : ContinuousOn (fun time => shapeChartAngle (unstableShape motion time index, stableShape motion time index)) times :=
    continuousOn_const.add (continuousOn_const.mul (shape.fst.sub shape.snd))
  exact (phaseContinuous.sub (continuousOn_const.mul angle)).sub composition

end EulerNonuniqueness.Paper
