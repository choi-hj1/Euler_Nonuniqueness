import EulerNonuniqueness.Section6.BoundaryQuadrupoleComplexMoment
import EulerNonuniqueness.Section6.PointComplexMomentAnisotropy
import EulerNonuniqueness.Section4.ReferenceConfinement

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.reference_literal_complex_moment_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {threshold constant time : ℝ}
    (evolution : FinitePatchEvolution scales motion 2) (inside : time ∈ Icc 0 2)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (constantNonnegative : 0 ≤ constant)
    (thresholdSmall : threshold ≤ 1 / 4) (coarse : ReferenceCoarseBounds scales motion threshold constant)
    (source : Fin count)
    (deformationSmall : constant * (scales.omega (source.val + 1))⁻¹ ^ 2 ≤ 1 / 16) :
    ‖∫ position, quadrupoleDensity scales motion time source position •
        (position - quadrupoleCenter motion time source) ^ 2‖ ≤
      16 * scales.circulation (source.val + 1) * scales.length (source.val + 1) ^ 2 +
      512 * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 *
        (constant * (scales.omega (source.val + 1))⁻¹ ^ 2) := by
  have bounds := coarse.2.1 time inside source
  have lengthPositive := scales.length_pos (source.val + 1)
  have lengthSquarePositive : 0 < scales.length (source.val + 1) ^ 2 := sq_pos_of_pos lengthPositive
  have differencePositive : 0 < diagonalDifference motion time source := by
    have lower := (le_div_iff₀ lengthSquarePositive).mp bounds.2.2.1
    nlinarith
  have differenceUpper : diagonalDifference motion time source ≤ 2 * scales.length (source.val + 1) ^ 2 :=
    (div_le_iff₀ lengthSquarePositive).mp bounds.2.2.2.1
  have radialUpper : radialShape motion time source ≤ 1 / 2 := by
    rw [radialShape_eq_unstable_add_stable]
    have first := (le_abs_self _).trans bounds.1
    have second := (le_abs_self _).trans bounds.2.1
    linarith
  obtain ⟨positiveBound, negativeBound⟩ := halfDiagonals_norm_le_of_reference_shape
    lengthPositive differencePositive differenceUpper radialUpper
  have pointIdentity : Section6.fourPointCenteredComplexMoment
      (fun patch => patchCentroid motion time source patch) =
        2 * ((positiveHalfDiagonal motion time source) ^ 2 - (negativeHalfDiagonal motion time source) ^ 2) := by
    simpa only [Section6.fourPointOddPart, positiveHalfDiagonal, negativeHalfDiagonal] using
      Section6.fourPointCenteredComplexMoment_eq_odd_difference (fun patch => patchCentroid motion time source patch)
  have pointBound : ‖Section6.fourPointCenteredComplexMoment
      (fun patch => patchCentroid motion time source patch)‖ ≤ 16 * scales.length (source.val + 1) ^ 2 := by
    rw [pointIdentity, norm_mul]
    norm_num only [Complex.norm_ofNat]
    have triangle := norm_sub_le ((positiveHalfDiagonal motion time source) ^ 2)
      ((negativeHalfDiagonal motion time source) ^ 2)
    rw [norm_pow, norm_pow] at triangle
    have positiveSquare := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr positiveBound
    have negativeSquare := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr negativeBound
    nlinarith
  have error := evolution.quadrupole_complex_second_moment_point_error inside amplitudePositive frequencyPositive
    ratioPositive source bounds.2.2.2.2.2 (by positivity) deformationSmall
  have triangle := norm_add_le
    ((∫ position, quadrupoleDensity scales motion time source position •
      (position - quadrupoleCenter motion time source) ^ 2) -
      scales.circulation (source.val + 1) • Section6.fourPointCenteredComplexMoment
        (fun patch => patchCentroid motion time source patch))
    (scales.circulation (source.val + 1) • Section6.fourPointCenteredComplexMoment
      (fun patch => patchCentroid motion time source patch))
  rw [sub_add_cancel, norm_smul, Real.norm_eq_abs,
    abs_of_pos (scales.circulation_pos frequencyPositive ratioPositive (source.val + 1))] at triangle
  have pointScaled := mul_le_mul_of_nonneg_left pointBound
    (scales.circulation_pos frequencyPositive ratioPositive (source.val + 1)).le
  exact triangle.trans ((add_le_add error pointScaled).trans_eq (by ring))

end EulerNonuniqueness.Paper
