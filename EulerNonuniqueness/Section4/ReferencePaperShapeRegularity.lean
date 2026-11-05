import EulerNonuniqueness.Section3.MovingMaterialCentroidRegularity
import EulerNonuniqueness.Section4.ReferencePaperShapeDerivative
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option synthInstance.maxHeartbeats 100000

theorem patchCentroid_contDiffAt {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    {time : ℝ} (index : Fin count) (patch : Fin 4)
    (inside : time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime) :
    ContDiffAt ℝ 1 (fun current => patchCentroid family.patchMotion current index patch) time := by
  have actual := (family.patch (finProdFinEquiv (index, patch))).centroid_contDiffAt inside
  apply actual.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun current => family.patchCentroid_eq current index patch

theorem halfDiagonals_contDiffAt {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    {time : ℝ} (index : Fin count)
    (inside : ∀ patch : Fin 4, time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime) :
    ContDiffAt ℝ 1 (fun current => positiveHalfDiagonal family.patchMotion current index) time ∧
      ContDiffAt ℝ 1 (fun current => negativeHalfDiagonal family.patchMotion current index) time := by
  constructor
  · unfold positiveHalfDiagonal
    simp only [div_eq_mul_inv]
    exact ((family.patchCentroid_contDiffAt index 0 (inside 0)).sub
      (family.patchCentroid_contDiffAt index 1 (inside 1))).mul contDiffAt_const
  · unfold negativeHalfDiagonal
    simp only [div_eq_mul_inv]
    exact ((family.patchCentroid_contDiffAt index 2 (inside 2)).sub
      (family.patchCentroid_contDiffAt index 3 (inside 3))).mul contDiffAt_const

theorem centroid_paper_shape_contDiffAt_of_upper {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) {time : ℝ} (index : Fin count)
    (inside : ∀ patch : Fin 4, time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (nonzero : positiveHalfDiagonal family.patchMotion time index ≠ 0)
    (upper : 0 < (negativeHalfDiagonal family.patchMotion time index /
      positiveHalfDiagonal family.patchMotion time index).im) :
    ContDiffAt ℝ 1 (fun current => (unstableShape family.patchMotion current index,
      stableShape family.patchMotion current index)) time := by
  obtain ⟨positiveSmooth, negativeSmooth⟩ := family.halfDiagonals_contDiffAt index inside
  have ratioSmooth : ContDiffAt ℝ 1 (fun current => negativeHalfDiagonal family.patchMotion current index /
      positiveHalfDiagonal family.patchMotion current index) time := by
    simpa only [div_eq_mul_inv] using negativeSmooth.mul (positiveSmooth.inv nonzero)
  have slit : negativeHalfDiagonal family.patchMotion time index /
      positiveHalfDiagonal family.patchMotion time index ∈ Complex.slitPlane := Or.inr upper.ne'
  have logSmooth : ContDiffAt ℝ 1 Complex.log (negativeHalfDiagonal family.patchMotion time index /
      positiveHalfDiagonal family.patchMotion time index) :=
    (Complex.contDiffAt_log (n := 1) slit).restrict_scalars ℝ
  have logarithm : ContDiffAt ℝ 1 (fun current => Complex.log (negativeHalfDiagonal family.patchMotion current index /
      positiveHalfDiagonal family.patchMotion current index)) time := by
    exact ContDiffAt.comp (𝕜 := ℝ) (n := 1) (g := Complex.log)
      (f := fun current => negativeHalfDiagonal family.patchMotion current index /
        positiveHalfDiagonal family.patchMotion current index) time logSmooth ratioSmooth
  have argument : ContDiffAt ℝ 1 (fun current => Complex.arg (negativeHalfDiagonal family.patchMotion current index /
      positiveHalfDiagonal family.patchMotion current index)) time := by
    simpa only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] using
      Complex.imCLM.contDiff.contDiffAt.comp time logarithm
  have denominatorNonzero : ‖positiveHalfDiagonal family.patchMotion time index‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr nonzero)
  have positiveNorm : ContDiffAt ℝ 1 (fun current => ‖positiveHalfDiagonal family.patchMotion current index‖ ^ 2) time :=
    (contDiff_norm_sq ℝ).contDiffAt.comp time positiveSmooth
  have negativeNorm : ContDiffAt ℝ 1 (fun current => ‖negativeHalfDiagonal family.patchMotion current index‖ ^ 2) time :=
    (contDiff_norm_sq ℝ).contDiffAt.comp time negativeSmooth
  have radial : ContDiffAt ℝ 1 (fun current => radialShape family.patchMotion current index) time := by
    unfold radialShape
    simp only [div_eq_mul_inv]
    exact ((negativeNorm.div positiveNorm denominatorNonzero).sub contDiffAt_const).mul contDiffAt_const
  have angular : ContDiffAt ℝ 1 (fun current => angularShape family.patchMotion current index) time := by
    unfold angularShape
    simp only [div_eq_mul_inv]
    exact ((contDiffAt_const.mul argument).sub contDiffAt_const).mul contDiffAt_const
  have unstable : ContDiffAt ℝ 1 (fun current => unstableShape family.patchMotion current index) time := by
    unfold unstableShape
    simp only [div_eq_mul_inv]
    exact (radial.add angular).mul contDiffAt_const
  have stable : ContDiffAt ℝ 1 (fun current => stableShape family.patchMotion current index) time := by
    unfold stableShape
    simp only [div_eq_mul_inv]
    exact (radial.sub angular).mul contDiffAt_const
  exact unstable.prodMk stable

theorem referencePointShapeVelocity_continuousOn {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) {scales : Scales} {horizon : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (index : Fin count)
    (inside : ∀ time ∈ Icc 0 horizon, ∀ patch : Fin 4,
      time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
        (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ time ∈ Icc 0 horizon, ∀ patch label,
      (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
      biotSavart (Paper.patchVorticity scales family.patchMotion time)
        ((family.patch (finProdFinEquiv (index, patch))).boundary time label))
    (upper : ∀ time ∈ Icc 0 horizon, 0 < (negativeHalfDiagonal family.patchMotion time index /
      positiveHalfDiagonal family.patchMotion time index).im)
    (small : ∀ time ∈ Icc 0 horizon,
      |unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| ≤ 1 / 4) :
    ContinuousOn (fun time => referencePointShapeVelocity scales family.patchMotion time index) (Icc 0 horizon) := by
  have equation (time : ℝ) (member : time ∈ Icc 0 horizon) :=
    family.centroid_paper_shape_hasDerivAt_of_upper evolution member index (inside time member)
      (material time member) (upper time member) (small time member)
  have continuousDerivative : ContinuousOn
      (deriv (fun current => (unstableShape family.patchMotion current index, stableShape family.patchMotion current index)))
      (Icc 0 horizon) := by
    intro time member
    have nonzero : positiveHalfDiagonal family.patchMotion time index ≠ 0 := by
      intro zero
      have positiveImaginary := upper time member
      simpa only [zero, div_zero, Complex.zero_im, lt_self_iff_false] using positiveImaginary
    have regularity := family.centroid_paper_shape_contDiffAt_of_upper index (inside time member) nonzero (upper time member)
    have derivativeContinuous : ContinuousAt
        (fderiv ℝ (fun current => (unstableShape family.patchMotion current index, stableShape family.patchMotion current index))) time :=
      (regularity.fderiv_right (m := 0) (by norm_num)).continuousAt
    exact ((ContinuousLinearMap.apply ℝ (ℝ × ℝ) (1 : ℝ)).continuous.continuousAt.comp derivativeContinuous).continuousWithinAt
  apply continuousDerivative.congr
  intro time member
  exact (equation time member).deriv.symm

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
