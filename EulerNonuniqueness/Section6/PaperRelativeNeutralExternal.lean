import EulerNonuniqueness.Section5.CascadeRelativeNeutralHistory
import EulerNonuniqueness.Section6.PaperExternalFirstMoment

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace EulerNonuniqueness.Paper

def quadrupoleCenteredExternalIncrement {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (index : Fin count) (time : ℝ) (patch : Fin 4) : ℂ :=
  biotSavart (externalPatchVorticity scales motion time index) (patchCentroid motion time index patch) -
    biotSavart (externalPatchVorticity scales motion time index) (quadrupoleCenter motion time index)

theorem FinitePatchEvolution.quadrupoleNeutralExternalVelocity_eq_centered_sum
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) :
    quadrupoleNeutralExternalVelocity scales motion index time =
      (1 / 4 : ℝ) • ∑ patch : Fin 4, patchSign patch •
        (quadrupoleCenteredExternalIncrement scales motion index time patch +
          quadrupoleExternalReceiverResidual scales motion time index patch) := by
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)
  have coefficient : (4 * scales.circulation (index.val + 1))⁻¹ * scales.circulation (index.val + 1) = (1 / 4 : ℝ) := by
    field_simp
    <;> ring
  rw [quadrupoleNeutralExternalVelocity,
    evolution.quadrupole_external_integral_eq_centroid_residual_sum inside amplitudePositive frequencyPositive ratioPositive,
    smul_smul, coefficient]
  congr 1
  simp only [Fin.sum_univ_four, patchSign, quadrupoleCenteredExternalIncrement]
  norm_num [show ¬(3 : Fin 4).val < 2 by decide]
  abel

theorem relative_quadrupoleNeutralExternalVelocity_eq_centered_sum
    {count : ℕ} {scales : Scales} {first second : PatchMotion count} {horizon time : ℝ}
    (firstEvolution : FinitePatchEvolution scales first horizon)
    (secondEvolution : FinitePatchEvolution scales second horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) :
    quadrupoleNeutralExternalVelocity scales first index time -
      quadrupoleNeutralExternalVelocity scales second index time =
    (1 / 4 : ℝ) • ∑ patch : Fin 4, patchSign patch •
      ((quadrupoleCenteredExternalIncrement scales first index time patch -
        quadrupoleCenteredExternalIncrement scales second index time patch) +
      (quadrupoleExternalReceiverResidual scales first time index patch -
        quadrupoleExternalReceiverResidual scales second time index patch)) := by
  rw [firstEvolution.quadrupoleNeutralExternalVelocity_eq_centered_sum inside amplitudePositive frequencyPositive ratioPositive,
    secondEvolution.quadrupoleNeutralExternalVelocity_eq_centered_sum inside amplitudePositive frequencyPositive ratioPositive,
    ← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro patch _
  rw [← smul_sub]
  congr 1
  abel

theorem relative_quadrupoleNeutralExternalVelocity_norm_le_centered_sum
    {count : ℕ} {scales : Scales} {first second : PatchMotion count} {horizon time : ℝ}
    (firstEvolution : FinitePatchEvolution scales first horizon)
    (secondEvolution : FinitePatchEvolution scales second horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) :
    ‖quadrupoleNeutralExternalVelocity scales first index time -
      quadrupoleNeutralExternalVelocity scales second index time‖ ≤
    (1 / 4 : ℝ) * ∑ patch : Fin 4,
      (‖quadrupoleCenteredExternalIncrement scales first index time patch -
        quadrupoleCenteredExternalIncrement scales second index time patch‖ +
      ‖quadrupoleExternalReceiverResidual scales first time index patch -
        quadrupoleExternalReceiverResidual scales second time index patch‖) := by
  rw [relative_quadrupoleNeutralExternalVelocity_eq_centered_sum firstEvolution secondEvolution inside
    amplitudePositive frequencyPositive ratioPositive index, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro patch _
  have sign : |patchSign patch| = 1 := by fin_cases patch <;> norm_num [patchSign]
  rw [norm_smul, Real.norm_eq_abs, sign, one_mul]
  exact norm_add_le _ _

end EulerNonuniqueness.Paper
