import EulerNonuniqueness.Section5.CascadePairedSaddleAdmissibility
import EulerNonuniqueness.Section6.PaperStraightenedShapeDynamics
import EulerNonuniqueness.Section4.ReferencePaperShapeRegularity

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem FiniteMovingPatchFamily.straightenedShape_contDiffAt_of_small
    {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) {graph coordinate : ℝ → ℝ}
    (index : Fin count) {time : ℝ}
    (inside : ∀ patch : Fin 4, time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (small : |unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| ≤ 1 / 4)
    (graphSmooth : ContDiffAt ℝ 1 graph (unstableShape family.patchMotion time index))
    (coordinateSmooth : ContDiffAt ℝ 1 coordinate (unstableShape family.patchMotion time index)) :
    ContDiffAt ℝ 1 (referenceStraightenedShape family.patchMotion graph coordinate index) time := by
  have upper := paper_shape_ratio_im_pos_of_small family.patchMotion time index small
  have nonzero : positiveHalfDiagonal family.patchMotion time index ≠ 0 := by
    intro zero
    simpa only [zero, div_zero, Complex.zero_im, lt_self_iff_false] using upper
  have raw := family.centroid_paper_shape_contDiffAt_of_upper index inside nonzero upper
  have unstableSmooth := contDiffAt_fst.comp time raw
  have stableSmooth := contDiffAt_snd.comp time raw
  simpa only [referenceStraightenedShape, localNormalFormChart, Function.comp_def] using
    (coordinateSmooth.comp time unstableSmooth).prodMk (stableSmooth.sub (graphSmooth.comp time unstableSmooth))

theorem exists_uniform_cascade_paired_chart_regularity {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
    ∀ {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count, ∀ finish : ℝ,
    finish ≤ path.stop →
    (∀ side, ∀ time ∈ Icc 0 finish,
      |unstableShape (cascadePairedMotion prepared side) time index| +
        |stableShape (cascadePairedMotion prepared side) time index| < radius) →
    let relative := fun time => referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time -
      referenceStraightenedShape prepared.reference graph coordinate index time
    ContinuousOn relative (Icc 0 finish) ∧ ContinuousOn (deriv relative) (Icc 0 finish) := by
  have nearby := ((graphSmooth.of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)).eventually (by norm_num)).and
    ((coordinateSmooth.of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)).eventually (by norm_num))
  obtain ⟨baseRadius, basePositive, baseInside⟩ := Metric.mem_nhds_iff.mp nearby
  let radius := min baseRadius (1 / 4)
  refine ⟨radius, by dsimp [radius]; positivity, min_le_right _ _, ?_⟩
  intro scales orbit sectionTime phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor monitor
    boundaryConstant count prepared path index finish finishBound small
  dsimp only
  have regular (side : Fin 2) (time : ℝ) (member : time ∈ Icc 0 finish) :
      ContDiffAt ℝ 1 (referenceStraightenedShape (cascadePairedMotion prepared side) graph coordinate index) time := by
    have pointSmall := small side time member
    have derivatives := baseInside (show unstableShape (cascadePairedMotion prepared side) time index ∈ Metric.ball (0 : ℝ) baseRadius by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
      exact (le_add_of_nonneg_right (abs_nonneg _)).trans_lt (pointSmall.trans_le (min_le_left _ _)))
    have rawSmall : |unstableShape (cascadePairedMotion prepared side) time index| +
        |stableShape (cascadePairedMotion prepared side) time index| ≤ 1 / 4 :=
      pointSmall.le.trans (min_le_right _ _)
    have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
      ⟨by linarith [member.1], by linarith [member.2, path.stopBound]⟩
    fin_cases side
    · exact prepared.trajectory.movingFamily.straightenedShape_contDiffAt_of_small index (fun _ => globalInside)
        rawSmall derivatives.1 derivatives.2
    · simp only [cascadePairedMotion, Fin.cases_succ, prepared.referenceIdentity] at rawSmall derivatives ⊢
      exact prepared.referenceWitness.trajectory.movingFamily.straightenedShape_contDiffAt_of_small index
        (fun _ => globalInside) rawSmall derivatives.1 derivatives.2
  have relativeRegular (time : ℝ) (member : time ∈ Icc 0 finish) :
      ContDiffAt ℝ 1 (fun current =>
        referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index current -
          referenceStraightenedShape prepared.reference graph coordinate index current) time :=
    (regular 0 time member).sub (regular 1 time member)
  constructor
  · exact fun time member => (relativeRegular time member).continuousAt.continuousWithinAt
  · intro time member
    have derivativeContinuous := ((relativeRegular time member).fderiv_right (m := 0) (by norm_num)).continuousAt
    exact ((ContinuousLinearMap.apply ℝ (ℝ × ℝ) (1 : ℝ)).continuous.continuousAt.comp derivativeContinuous).continuousWithinAt

end EulerNonuniqueness.Paper
