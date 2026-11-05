import EulerNonuniqueness.Section1.IndividualPatchInteractionSum

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.Paper

theorem Scales.sum_fourPatchInteractionWeight_le_omega {count : ℕ} (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (strainSmall : scales.strain ≤ 1) (receiver : Fin count) :
    (∑ source : Fin (count * 4),
      scales.circulation ((finProdFinEquiv.symm source).1.val + 1) /
        scales.individualInteractionDistance (receiver.val + 1) ((finProdFinEquiv.symm source).1.val + 1) ^ 2) ≤
      (80000 * Real.pi + 2304) * scales.omega (receiver.val + 1) := by
  have ratioPower : 1 ≤ scales.ratio ^ (receiver.val + 1) := one_le_pow₀ (by linarith)
  have omegaLarge : 1 ≤ scales.omega (receiver.val + 1) := by
    calc
      1 = (1 : ℝ) * 1 := by ring
      _ ≤ scales.frequency * scales.ratio ^ (receiver.val + 1) :=
        mul_le_mul frequencyBound ratioPower zero_le_one (zero_le_one.trans frequencyBound)
      _ = _ := rfl
  calc
    _ ≤ 80000 * Real.pi * scales.omega (receiver.val + 1) + 2304 * scales.strain :=
      scales.sum_fourPatchInteractionWeight_le frequencyBound ratioBound alphaPositive receiver
    _ ≤ 80000 * Real.pi * scales.omega (receiver.val + 1) + 2304 * scales.omega (receiver.val + 1) := by
      gcongr
      exact strainSmall.trans omegaLarge
    _ = _ := by ring

end EulerNonuniqueness.Paper
