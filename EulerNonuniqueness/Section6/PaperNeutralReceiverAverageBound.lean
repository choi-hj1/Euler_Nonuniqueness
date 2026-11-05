import EulerNonuniqueness.Section6.PaperNeutralPointReceiverSplit

noncomputable section

namespace EulerNonuniqueness.Section6

theorem fourPointSignedAverage_norm_le_quarter_sum (values : FourPointConfiguration) :
    ‖fourPointSignedAverageCLM values‖ ≤ (1 / 4 : ℝ) * ∑ patch : Fin 4, ‖values patch‖ := by
  rw [fourPointSignedAverageCLM_apply, norm_div, Complex.norm_ofNat]
  have summed : ‖fourPointSignedMoment values‖ ≤ ∑ patch : Fin 4, ‖values patch‖ := by
    unfold fourPointSignedMoment
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro patch _
    have sign : ‖(fourPointSign patch : ℂ)‖ = 1 := by fin_cases patch <;> norm_num [fourPointSign]
    simp only [norm_mul, sign, one_mul, le_refl]
  linarith

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem quadrupoleExternalReceiverAverage_relative_norm_le_quarter_sum
    {count : ℕ} (scales : Scales) (first second : PatchMotion count) (index : Fin count) (time : ℝ) :
    ‖quadrupoleExternalReceiverAverage scales first index time - quadrupoleExternalReceiverAverage scales second index time‖ ≤
      (1 / 4 : ℝ) * ∑ patch : Fin 4,
        ‖quadrupoleExternalReceiverResidual scales first time index patch -
          quadrupoleExternalReceiverResidual scales second time index patch‖ := by
  have identity : quadrupoleExternalReceiverAverage scales first index time -
      quadrupoleExternalReceiverAverage scales second index time =
      fourPointSignedAverageCLM (fun patch => quadrupoleExternalReceiverResidual scales first time index patch -
        quadrupoleExternalReceiverResidual scales second time index patch) := by
    rw [quadrupoleExternalReceiverAverage, quadrupoleExternalReceiverAverage, ← map_sub]
    rfl
  rw [identity]
  exact fourPointSignedAverage_norm_le_quarter_sum _

end EulerNonuniqueness.Paper
