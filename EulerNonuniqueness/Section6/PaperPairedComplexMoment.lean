import EulerNonuniqueness.Section6.PaperPairedSourceStrain
import EulerNonuniqueness.Section6.BoundaryQuadrupoleComplexMoment

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.quadrupole_complex_moment_paired_error
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count)
    (firstCenter secondCenter firstSeparation secondSeparation : ℂ)
    (positionsEquation : Section6.relabelNegativePoints (fun patch => patchCentroid motion time index patch) =
      Section6.twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation)
    (control : ∀ patch, BoundaryCloseToCircle scales motion time index patch deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16) :
    ‖(∫ position, quadrupoleDensity scales motion time index position •
        (position - quadrupoleCenter motion time index) ^ 2) -
      scales.circulation (index.val + 1) • ((firstCenter - secondCenter) * (firstSeparation - secondSeparation))‖ ≤
      512 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation := by
  have estimate := evolution.quadrupole_complex_second_moment_point_error inside amplitudePositive frequencyPositive
    ratioPositive index control nonnegative small
  dsimp only at estimate
  have pointIdentity : Section6.fourPointCenteredComplexMoment (fun patch => patchCentroid motion time index patch) =
      (firstCenter - secondCenter) * (firstSeparation - secondSeparation) := by
    rw [← Section6.fourPointCenteredComplexMoment_negativeLabelSwap, positionsEquation,
      Section6.twoDipole_centered_complex_moment]
  rw [pointIdentity] at estimate
  exact estimate

theorem FinitePatchEvolution.quadrupole_paired_normalized_moment_error
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count)
    (firstCenter secondCenter firstSeparation secondSeparation targetMoment : ℂ)
    (positionsEquation : Section6.relabelNegativePoints (fun patch => patchCentroid motion time index patch) =
      Section6.twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation)
    (control : ∀ patch, BoundaryCloseToCircle scales motion time index patch deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16) :
    scales.circulation (index.val + 1) *
        ‖(firstCenter - secondCenter) * (firstSeparation - secondSeparation) -
          targetMoment / (scales.circulation (index.val + 1) : ℂ)‖ ≤
      ‖(∫ position, quadrupoleDensity scales motion time index position •
        (position - quadrupoleCenter motion time index) ^ 2) - targetMoment‖ +
        512 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation := by
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)
  have estimate := evolution.quadrupole_complex_moment_paired_error inside amplitudePositive frequencyPositive ratioPositive
    index firstCenter secondCenter firstSeparation secondSeparation positionsEquation control nonnegative small
  have identity : (scales.circulation (index.val + 1) : ℂ) *
      ((firstCenter - secondCenter) * (firstSeparation - secondSeparation) -
        targetMoment / (scales.circulation (index.val + 1) : ℂ)) =
      scales.circulation (index.val + 1) • ((firstCenter - secondCenter) * (firstSeparation - secondSeparation)) - targetMoment := by
    rw [Complex.real_smul]
    field_simp [Complex.ofReal_ne_zero.mpr circulationPositive.ne']
    <;> ring
  have normIdentity : scales.circulation (index.val + 1) *
      ‖(firstCenter - secondCenter) * (firstSeparation - secondSeparation) -
        targetMoment / (scales.circulation (index.val + 1) : ℂ)‖ =
      ‖scales.circulation (index.val + 1) • ((firstCenter - secondCenter) * (firstSeparation - secondSeparation)) - targetMoment‖ := by
    calc
      _ = ‖(scales.circulation (index.val + 1) : ℂ)‖ *
          ‖(firstCenter - secondCenter) * (firstSeparation - secondSeparation) -
            targetMoment / (scales.circulation (index.val + 1) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos circulationPositive]
      _ = _ := by rw [← norm_mul, identity]
  rw [normIdentity]
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (scales.circulation (index.val + 1) • ((firstCenter - secondCenter) * (firstSeparation - secondSeparation)))
    (∫ position, quadrupoleDensity scales motion time index position • (position - quadrupoleCenter motion time index) ^ 2)
    targetMoment
  rw [norm_sub_rev] at estimate
  exact triangle.trans ((add_le_add estimate le_rfl).trans_eq (add_comm _ _))

end EulerNonuniqueness.Paper
