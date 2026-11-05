import EulerNonuniqueness.Section4.PaperCoarseUpperBranch
import EulerNonuniqueness.Section6.PaperCentroidEndpoints

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem paper_shape_continuousOn_of_centroids {count : ℕ} (motion : PatchMotion count)
    {times : Set ℝ} (index : Fin count)
    (centroids : ∀ patch : Fin 4,
      ContinuousOn (fun time => patchCentroid motion time index patch) times)
    (small : ∀ time ∈ times,
      |unstableShape motion time index| + |stableShape motion time index| ≤ 1 / 4) :
    ContinuousOn (fun time => (unstableShape motion time index,
      stableShape motion time index)) times := by
  have positive : ContinuousOn (fun time => positiveHalfDiagonal motion time index) times := by
    unfold positiveHalfDiagonal
    exact ((centroids 0).sub (centroids 1)).div_const 2
  have negative : ContinuousOn (fun time => negativeHalfDiagonal motion time index) times := by
    unfold negativeHalfDiagonal
    exact ((centroids 2).sub (centroids 3)).div_const 2
  have upper (time : ℝ) (member : time ∈ times) :=
    paper_shape_ratio_im_pos_of_small motion time index (small time member)
  have nonzero (time : ℝ) (member : time ∈ times) :
      positiveHalfDiagonal motion time index ≠ 0 := by
    intro zero
    have impossible := upper time member
    simpa only [zero, div_zero, Complex.zero_im, lt_self_iff_false] using impossible
  have ratio := negative.div positive nonzero
  have argument : ContinuousOn (fun time => Complex.arg
      (negativeHalfDiagonal motion time index / positiveHalfDiagonal motion time index)) times := by
    intro time member
    have argumentContinuous : ContinuousAt Complex.arg
        (negativeHalfDiagonal motion time index / positiveHalfDiagonal motion time index) :=
      Complex.continuousAt_arg (Or.inr (upper time member).ne')
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun current => negativeHalfDiagonal motion current index /
        positiveHalfDiagonal motion current index) argumentContinuous (ratio time member)
  have radial : ContinuousOn (fun time => radialShape motion time index) times := by
    unfold radialShape
    exact (((negative.norm.pow 2).div (positive.norm.pow 2)
      (fun time member => pow_ne_zero 2 (norm_ne_zero_iff.mpr (nonzero time member)))).sub
      continuousOn_const).div_const _
  have angular : ContinuousOn (fun time => angularShape motion time index) times := by
    unfold angularShape
    exact ((continuousOn_const.mul argument).sub continuousOn_const).div_const _
  exact ((radial.add angular).div_const 2).prodMk ((radial.sub angular).div_const 2)

theorem FinitePatchEvolution.paper_shape_continuousOn_of_boundary_gaps
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (horizonPositive : 0 < horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (radiusPositive : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
    (control : ∀ current ∈ Icc 0 horizon, ∀ index patch,
      ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle scales motion current index patch bound)
    (separated : ∀ current ∈ Icc 0 horizon, ∀ (index other : Fin count) (patch otherPatch : Fin 4),
      (other, otherPatch) ≠ (index, patch) →
      8 * scales.radius (index.val + 1) + 8 * scales.radius (other.val + 1) <
        dist (motion.boundary current index patch 0) (motion.boundary current other otherPatch 0))
    (index : Fin count)
    (small : ∀ time ∈ Icc 0 horizon,
      |unstableShape motion time index| + |stableShape motion time index| ≤ 1 / 4) :
    ContinuousOn (fun time => (unstableShape motion time index,
      stableShape motion time index)) (Icc 0 horizon) := by
  apply paper_shape_continuousOn_of_centroids motion index
  · intro patch
    exact (evolution.patchCentroid_closed_derivative_of_boundary_gaps horizonPositive
      amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index patch).1
  · exact small

end EulerNonuniqueness.Paper
