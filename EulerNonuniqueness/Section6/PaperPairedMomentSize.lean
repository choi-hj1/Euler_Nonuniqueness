import EulerNonuniqueness.Section6.PaperPairedComplexMoment

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.quadrupole_complex_moment_paired_norm_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count)
    (firstCenter secondCenter firstSeparation secondSeparation : ℂ)
    (positionsEquation : Section6.relabelNegativePoints (fun patch => patchCentroid motion time index patch) =
      Section6.twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation)
    (control : ∀ patch, BoundaryCloseToCircle scales motion time index patch deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16) :
    ‖∫ position, quadrupoleDensity scales motion time index position •
        (position - quadrupoleCenter motion time index) ^ 2‖ ≤
      scales.circulation (index.val + 1) * ‖firstCenter - secondCenter‖ *
        (‖firstSeparation‖ + ‖secondSeparation‖) +
      512 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation := by
  have comparison := evolution.quadrupole_complex_moment_paired_error inside amplitudePositive frequencyPositive
    ratioPositive index firstCenter secondCenter firstSeparation secondSeparation positionsEquation control nonnegative small
  have circulationNonnegative := (scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)).le
  have pointBound : ‖scales.circulation (index.val + 1) •
      ((firstCenter - secondCenter) * (firstSeparation - secondSeparation))‖ ≤
      scales.circulation (index.val + 1) * ‖firstCenter - secondCenter‖ *
        (‖firstSeparation‖ + ‖secondSeparation‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg circulationNonnegative, norm_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
  have triangle := norm_sub_le
    ((∫ position, quadrupoleDensity scales motion time index position •
      (position - quadrupoleCenter motion time index) ^ 2) -
      scales.circulation (index.val + 1) • ((firstCenter - secondCenter) * (firstSeparation - secondSeparation)))
    (-(scales.circulation (index.val + 1) • ((firstCenter - secondCenter) * (firstSeparation - secondSeparation))))
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at triangle
  exact triangle.trans ((add_le_add comparison pointBound).trans_eq (add_comm _ _))

theorem FinitePatchEvolution.quadrupole_outgoing_initial_moment_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation distance : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count)
    (firstCenter secondCenter firstSeparation secondSeparation : ℂ)
    (positionsEquation : Section6.relabelNegativePoints (fun patch => patchCentroid motion time index patch) =
      Section6.twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation)
    (control : ∀ patch, BoundaryCloseToCircle scales motion time index patch deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16) (distanceNonnegative : 0 ≤ distance)
    (centerBound : ‖firstCenter - secondCenter‖ ≤ (5 / 4 : ℝ) * scales.length (index.val + 1) * distance)
    (firstBound : ‖firstSeparation‖ ≤ 2 * scales.length (index.val + 1))
    (secondBound : ‖secondSeparation‖ ≤ 2 * scales.length (index.val + 1)) :
    ‖∫ position, quadrupoleDensity scales motion time index position •
        (position - quadrupoleCenter motion time index) ^ 2‖ ≤
      5 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2 * distance +
      512 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation := by
  have estimate := evolution.quadrupole_complex_moment_paired_norm_bound inside amplitudePositive frequencyPositive
    ratioPositive index firstCenter secondCenter firstSeparation secondSeparation positionsEquation control nonnegative small
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)
  have lengthPositive := scales.length_pos (index.val + 1)
  apply estimate.trans
  apply add_le_add_right
  calc
    _ ≤ scales.circulation (index.val + 1) * ((5 / 4 : ℝ) * scales.length (index.val + 1) * distance) *
        (2 * scales.length (index.val + 1) + 2 * scales.length (index.val + 1)) := by gcongr
    _ = _ := by ring

end EulerNonuniqueness.Paper
