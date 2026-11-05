import EulerNonuniqueness.Section5.CascadePairedChartRegularity
import EulerNonuniqueness.Section6.PaperCorrectedPhaseDynamics

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

def geometricCorrectedPhaseVelocity {count : ℕ} (correction : ℝ → ℝ) (motion : PatchMotion count)
    (index : Fin count) (time : ℝ) : ℝ :=
  (deriv (fun current => positiveHalfDiagonal motion current index) time / positiveHalfDiagonal motion time index).im -
    (Real.sqrt 2 - 1) / 4 * Real.sqrt 2 *
      (deriv (fun current => unstableShape motion current index) time - deriv (fun current => stableShape motion current index) time) -
    deriv correction (unstableShape motion time index) * deriv (fun current => unstableShape motion current index) time

theorem FiniteMovingPatchFamily.correctedPaperPhase_hasDerivAt_geometric
    {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) (correction phase : ℝ → ℝ)
    (index : Fin count) {time : ℝ}
    (inside : ∀ patch : Fin 4, time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (small : |unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| ≤ 1 / 4)
    (correctionDifferentiable : DifferentiableAt ℝ correction (unstableShape family.patchMotion time index))
    (phaseEquation : HasDerivAt phase
      (deriv (fun current => positiveHalfDiagonal family.patchMotion current index) time /
        positiveHalfDiagonal family.patchMotion time index).im time) :
    HasDerivAt (correctedPaperPhase correction phase family.patchMotion index)
      (geometricCorrectedPhaseVelocity correction family.patchMotion index time) time := by
  have upper := paper_shape_ratio_im_pos_of_small family.patchMotion time index small
  have nonzero : positiveHalfDiagonal family.patchMotion time index ≠ 0 := by
    intro zero
    simpa only [zero, div_zero, Complex.zero_im, lt_self_iff_false] using upper
  have raw := family.centroid_paper_shape_contDiffAt_of_upper index inside nonzero upper
  have unstable : ContDiffAt ℝ 1 (fun current => unstableShape family.patchMotion current index) time :=
    contDiffAt_fst.comp time raw
  have stable : ContDiffAt ℝ 1 (fun current => stableShape family.patchMotion current index) time :=
    contDiffAt_snd.comp time raw
  have unstableDerivative := (unstable.differentiableAt (by norm_num)).hasDerivAt
  have stableDerivative := (stable.differentiableAt (by norm_num)).hasDerivAt
  have angular := ((unstableDerivative.sub stableDerivative).const_mul (Real.sqrt 2)).const_add Real.pi
  have actual := (phaseEquation.sub (angular.const_mul ((Real.sqrt 2 - 1) / 4))).sub
    (correctionDifferentiable.hasDerivAt.comp time unstableDerivative)
  convert actual using 1 <;>
    dsimp only [correctedPaperPhase, geometricCorrectedPhaseVelocity, shapeChartAngle] <;> ring

theorem FiniteMovingPatchFamily.geometricCorrectedPhaseVelocity_continuousOn
    {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) (correction : ℝ → ℝ)
    (index : Fin count) {times : Set ℝ}
    (inside : ∀ time ∈ times, ∀ patch : Fin 4,
      time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
        (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (small : ∀ time ∈ times, |unstableShape family.patchMotion time index| +
      |stableShape family.patchMotion time index| ≤ 1 / 4)
    (correctionSmooth : ∀ time ∈ times, ContDiffAt ℝ 2 correction (unstableShape family.patchMotion time index)) :
    ContinuousOn (geometricCorrectedPhaseVelocity correction family.patchMotion index) times := by
  intro time member
  have upper := paper_shape_ratio_im_pos_of_small family.patchMotion time index (small time member)
  have nonzero : positiveHalfDiagonal family.patchMotion time index ≠ 0 := by
    intro zero
    simpa only [zero, div_zero, Complex.zero_im, lt_self_iff_false] using upper
  have raw := family.centroid_paper_shape_contDiffAt_of_upper index (inside time member) nonzero upper
  have positive := (family.halfDiagonals_contDiffAt index (inside time member)).1
  have unstable : ContDiffAt ℝ 1 (fun current => unstableShape family.patchMotion current index) time :=
    contDiffAt_fst.comp time raw
  have stable : ContDiffAt ℝ 1 (fun current => stableShape family.patchMotion current index) time :=
    contDiffAt_snd.comp time raw
  have derivativeContinuous {function : ℝ → ℝ} (regular : ContDiffAt ℝ 1 function time) :
      ContinuousAt (deriv function) time := by
    have continuous := (regular.fderiv_right (m := 0) (by norm_num)).continuousAt
    exact (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).continuous.continuousAt.comp continuous
  have positiveDerivativeContinuous : ContinuousAt (deriv (fun current => positiveHalfDiagonal family.patchMotion current index)) time := by
    have continuous := (positive.fderiv_right (m := 0) (by norm_num)).continuousAt
    exact (ContinuousLinearMap.apply ℝ ℂ (1 : ℝ)).continuous.continuousAt.comp continuous
  have correctionDerivativeContinuous : ContinuousAt (deriv correction) (unstableShape family.patchMotion time index) := by
    have regular := ((correctionSmooth time member).fderiv_right (m := 1) (by norm_num)).continuousAt
    exact (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).continuous.continuousAt.comp regular
  have actual := ((Complex.continuous_im.continuousAt.comp
    (positiveDerivativeContinuous.div positive.continuousAt nonzero)).sub
    ((show ContinuousAt (fun _ : ℝ => (Real.sqrt 2 - 1) / 4 * Real.sqrt 2) time from continuousAt_const).mul
      ((derivativeContinuous unstable).sub (derivativeContinuous stable)))).sub
    ((correctionDerivativeContinuous.comp (f := fun current => unstableShape family.patchMotion current index)
      unstable.continuousAt).mul (derivativeContinuous unstable))
  exact actual.continuousWithinAt

end EulerNonuniqueness.Paper
