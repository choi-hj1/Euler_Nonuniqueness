import EulerNonuniqueness.Section6.PaperCentroidForcingContinuity
import EulerNonuniqueness.Section6.FullPointForcingContinuity
import EulerNonuniqueness.Section4.PaperShapeContinuity
import EulerNonuniqueness.Section4.ReferenceComputedShapeEquation

noncomputable section

open Set EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.referencePointShapeForcing_continuousOn_of_boundary_gaps
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
    (noncollision : ∀ time ∈ Icc 0 horizon,
      FourPointNoncollision (fun patch => patchCentroid motion time index patch))
    (small : ∀ time ∈ Icc 0 horizon,
      |unstableShape motion time index| + |stableShape motion time index| ≤ 1 / 4) :
    ContinuousOn (fun time => referencePointShapeForcing scales motion time index) (Icc 0 horizon) := by
  have positions : ContinuousOn (fun time patch => patchCentroid motion time index patch) (Icc 0 horizon) :=
    continuousOn_pi.mpr fun patch => (evolution.patchCentroid_closed_derivative_of_boundary_gaps
      horizonPositive amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index patch).1
  have forcing : ContinuousOn (fun time => quadrupoleCentroidForcing scales motion time index) (Icc 0 horizon) :=
    continuousOn_pi.mpr fun patch => evolution.quadrupoleCentroidForcing_continuousOn_of_boundary_gaps
      horizonPositive amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index noncollision patch
  have annulus (time : ℝ) (member : time ∈ Icc 0 horizon) :=
    pointShapeChart_reference_annulus (positiveHalfDiagonal motion time index)
      (negativeHalfDiagonal motion time index) (by
        rw [pointShapeChart_eq_paper_shape_of_upper motion time index
          (paper_shape_ratio_im_pos_of_small motion time index (small time member))]
        exact small time member)
  have positiveNonzero (time : ℝ) (member : time ∈ Icc 0 horizon) := (annulus time member).1
  have negativeNonzero (time : ℝ) (member : time ∈ Icc 0 horizon) := (annulus time member).2.1
  have squaresNonzero (time : ℝ) (member : time ∈ Icc 0 horizon) :
      star (positiveHalfDiagonal motion time index) ^ 2 - star (negativeHalfDiagonal motion time index) ^ 2 ≠ 0 := by
    intro zero
    have equal := congrArg norm (sub_eq_zero.mp zero)
    simp only [norm_pow, norm_star] at equal
    have positive := norm_pos_iff.mpr (positiveNonzero time member)
    have bound := (div_le_iff₀ positive).mp (annulus time member).2.2.2
    nlinarith only [equal, bound, positive, norm_nonneg (negativeHalfDiagonal motion time index)]
  have oddContinuous : Continuous (fourPointOddPart : FourPointConfiguration → ℂ × ℂ) := by
    unfold fourPointOddPart
    fun_prop
  have odd := oddContinuous.comp_continuousOn positions
  have total := fourPointTotalOddForcing_continuousOn
    (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
    positions forcing noncollision positiveNonzero negativeNonzero squaresNonzero
  exact pointShapeForcing_continuousOn odd.fst odd.snd total.fst total.snd positiveNonzero negativeNonzero

end EulerNonuniqueness.Paper
