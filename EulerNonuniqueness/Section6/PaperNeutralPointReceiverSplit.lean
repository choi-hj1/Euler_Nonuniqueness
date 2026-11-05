import EulerNonuniqueness.Section6.PaperRelativeNeutralExternal
import EulerNonuniqueness.Section6.PaperRelativeNeutralPointSeries

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

private theorem real_signed_average_eq (values : Fin 4 → ℂ) :
    (1 / 4 : ℝ) • ∑ patch : Fin 4, patchSign patch • values patch = fourPointSignedAverageCLM values := by
  rw [fourPointSignedAverageCLM_apply]
  have sign (patch : Fin 4) : patchSign patch = fourPointSign patch := rfl
  simp_rw [sign]
  simp only [fourPointSignedMoment, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

private theorem centered_signed_average_add (values residual : Fin 4 → ℂ) (center : ℂ) :
    fourPointSignedAverageCLM (fun patch => values patch - center + residual patch) =
      fourPointSignedAverageCLM values + fourPointSignedAverageCLM residual := by
  simp only [fourPointSignedAverageCLM_apply]
  norm_num [fourPointSignedMoment, fourPointSign, Fin.sum_univ_succ]
  ring

def quadrupoleExternalReceiverAverage {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (index : Fin count) (time : ℝ) : ℂ :=
  fourPointSignedAverageCLM (fun patch => quadrupoleExternalReceiverResidual scales motion time index patch)

theorem FinitePatchEvolution.quadrupoleNeutralExternalVelocity_eq_point_receiver
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) :
    quadrupoleNeutralExternalVelocity scales motion index time =
      quadrupoleExternalPointAverage scales motion index time + quadrupoleExternalReceiverAverage scales motion index time := by
  have averageForm : quadrupoleNeutralExternalVelocity scales motion index time =
      fourPointSignedAverageCLM (fun patch => quadrupoleCenteredExternalIncrement scales motion index time patch +
        quadrupoleExternalReceiverResidual scales motion time index patch) := by
    rw [evolution.quadrupoleNeutralExternalVelocity_eq_centered_sum inside amplitudePositive frequencyPositive ratioPositive,
      real_signed_average_eq]
  rw [averageForm]
  exact centered_signed_average_add
    (fun patch => biotSavart (externalPatchVorticity scales motion time index) (patchCentroid motion time index patch))
    (fun patch => quadrupoleExternalReceiverResidual scales motion time index patch)
    (biotSavart (externalPatchVorticity scales motion time index) (quadrupoleCenter motion time index))

theorem relative_quadrupoleNeutralExternalVelocity_norm_le_point_receiver
    {count : ℕ} {scales : Scales} {first second : PatchMotion count} {horizon time : ℝ}
    (firstEvolution : FinitePatchEvolution scales first horizon)
    (secondEvolution : FinitePatchEvolution scales second horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) :
    ‖quadrupoleNeutralExternalVelocity scales first index time - quadrupoleNeutralExternalVelocity scales second index time‖ ≤
      ‖quadrupoleExternalPointAverage scales first index time - quadrupoleExternalPointAverage scales second index time‖ +
      ‖quadrupoleExternalReceiverAverage scales first index time - quadrupoleExternalReceiverAverage scales second index time‖ := by
  rw [firstEvolution.quadrupoleNeutralExternalVelocity_eq_point_receiver inside amplitudePositive frequencyPositive ratioPositive,
    secondEvolution.quadrupoleNeutralExternalVelocity_eq_point_receiver inside amplitudePositive frequencyPositive ratioPositive]
  have identity (first second third fourth : ℂ) : (first + second) - (third + fourth) =
      (first - third) + (second - fourth) := by ring
  rw [identity]
  exact norm_add_le _ _

end EulerNonuniqueness.Paper
