import EulerNonuniqueness.Section4.PaperShapeForcingContinuity
import EulerNonuniqueness.Section6.PaperCorrectedPhaseDynamics

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem correctedPaperPhaseForcing_continuousOn_of_total
    {count : ℕ} (scales : Scales) (motion : PatchMotion count) (correction : ℝ → ℝ)
    (index : Fin count) {times : Set ℝ}
    (positions : ∀ patch : Fin 4, ContinuousOn (fun time => patchCentroid motion time index patch) times)
    (total : ContinuousOn (fun time => fourPointTotalOddForcing
      (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
      (fun patch => patchCentroid motion time index patch) (quadrupoleCentroidForcing scales motion time index)) times)
    (pointForcing : ContinuousOn (fun time => referencePointShapeForcing scales motion time index) times)
    (small : ∀ time ∈ times, |unstableShape motion time index| + |stableShape motion time index| ≤ 1 / 4)
    (correctionSmooth : ∀ time ∈ times, ContDiffAt ℝ 2 correction (unstableShape motion time index)) :
    ContinuousOn (correctedPaperPhaseForcing scales correction motion index) times := by
  have positive : ContinuousOn (fun time => positiveHalfDiagonal motion time index) times := by
    unfold positiveHalfDiagonal
    exact ((positions 0).sub (positions 1)).div_const 2
  have nonzero (time : ℝ) (inside : time ∈ times) : positiveHalfDiagonal motion time index ≠ 0 := by
    have upper := paper_shape_ratio_im_pos_of_small motion time index (small time inside)
    intro zero
    simpa only [zero, div_zero, Complex.zero_im, lt_self_iff_false] using upper
  have shape := paper_shape_continuousOn_of_centroids motion index positions small
  have correctionDerivative : ContinuousOn (fun time => deriv correction (unstableShape motion time index)) times := by
    intro time inside
    have actual := ((correctionSmooth time inside).fderiv_right (m := 1) (by norm_num)).continuousAt
    have derivative := (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).continuous.continuousAt.comp actual
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun current : ℝ => unstableShape motion current index) derivative (shape.fst time inside)
  have logarithm := Complex.continuous_im.comp_continuousOn (total.fst.div positive nonzero)
  have angular : ContinuousOn (fun time => (Real.sqrt 2 - 1) / 4 * Real.sqrt 2 *
      ((referencePointShapeForcing scales motion time index).1 - (referencePointShapeForcing scales motion time index).2)) times :=
    continuousOn_const.mul (pointForcing.fst.sub pointForcing.snd)
  have corrected := logarithm.sub angular |>.sub (correctionDerivative.mul pointForcing.fst)
  exact corrected

theorem FinitePatchEvolution.correctedPaperPhaseForcing_continuousOn_of_boundary_gaps
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
    (correction : ℝ → ℝ) (index : Fin count)
    (noncollision : ∀ time ∈ Icc 0 horizon, FourPointNoncollision (fun patch => patchCentroid motion time index patch))
    (small : ∀ time ∈ Icc 0 horizon, |unstableShape motion time index| + |stableShape motion time index| ≤ 1 / 4)
    (correctionSmooth : ∀ time ∈ Icc 0 horizon, ContDiffAt ℝ 2 correction (unstableShape motion time index)) :
    ContinuousOn (correctedPaperPhaseForcing scales correction motion index) (Icc 0 horizon) := by
  have positions : ContinuousOn (fun time patch => patchCentroid motion time index patch) (Icc 0 horizon) :=
    continuousOn_pi.mpr fun patch => (evolution.patchCentroid_closed_derivative_of_boundary_gaps
      horizonPositive amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index patch).1
  have forcing : ContinuousOn (fun time => quadrupoleCentroidForcing scales motion time index) (Icc 0 horizon) :=
    continuousOn_pi.mpr fun patch => evolution.quadrupoleCentroidForcing_continuousOn_of_boundary_gaps
      horizonPositive amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index noncollision patch
  have annulus (time : ℝ) (inside : time ∈ Icc 0 horizon) :=
    pointShapeChart_reference_annulus (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index) (by
      rw [pointShapeChart_eq_paper_shape_of_upper motion time index (paper_shape_ratio_im_pos_of_small motion time index (small time inside))]
      exact small time inside)
  have positiveNonzero (time : ℝ) (inside : time ∈ Icc 0 horizon) := (annulus time inside).1
  have negativeNonzero (time : ℝ) (inside : time ∈ Icc 0 horizon) := (annulus time inside).2.1
  have squaresNonzero (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      star (positiveHalfDiagonal motion time index) ^ 2 - star (negativeHalfDiagonal motion time index) ^ 2 ≠ 0 := by
    intro zero
    have equal := congrArg norm (sub_eq_zero.mp zero)
    simp only [norm_pow, norm_star] at equal
    have positive := norm_pos_iff.mpr (positiveNonzero time inside)
    have bound := (div_le_iff₀ positive).mp (annulus time inside).2.2.2
    nlinarith only [equal, bound, positive, norm_nonneg (negativeHalfDiagonal motion time index)]
  have oddContinuous : Continuous (fourPointOddPart : FourPointConfiguration → ℂ × ℂ) := by
    unfold fourPointOddPart
    fun_prop
  have odd := oddContinuous.comp_continuousOn positions
  have total := fourPointTotalOddForcing_continuousOn
    (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
    positions forcing noncollision positiveNonzero negativeNonzero squaresNonzero
  have point := evolution.referencePointShapeForcing_continuousOn_of_boundary_gaps horizonPositive
    amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index noncollision small
  exact correctedPaperPhaseForcing_continuousOn_of_total scales motion correction index
    (fun patch => (continuousOn_pi.mp positions) patch) total point small correctionSmooth

end EulerNonuniqueness.Paper
