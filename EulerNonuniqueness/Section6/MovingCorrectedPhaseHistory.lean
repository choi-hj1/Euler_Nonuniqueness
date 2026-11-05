import EulerNonuniqueness.Section6.MovingCorrectedPhaseRegularity

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem FiniteMovingPatchFamily.correctedPaperPhase_geometric_original_history
    {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) (correction phase : ℝ → ℝ)
    (index : Fin count) {finish : ℝ} (finishNonnegative : 0 ≤ finish)
    (inside : ∀ time ∈ Icc 0 finish, ∀ patch : Fin 4,
      time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
        (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (small : ∀ time ∈ Icc 0 finish, |unstableShape family.patchMotion time index| +
      |stableShape family.patchMotion time index| ≤ 1 / 4)
    (correctionSmooth : ∀ time ∈ Icc 0 finish, ContDiffAt ℝ 2 correction (unstableShape family.patchMotion time index))
    (phaseEquation : ∀ time ∈ Icc 0 finish, HasDerivAt phase
      (deriv (fun current => positiveHalfDiagonal family.patchMotion current index) time /
        positiveHalfDiagonal family.patchMotion time index).im time) :
    correctedPaperPhase correction phase family.patchMotion index finish -
      correctedPaperPhase correction phase family.patchMotion index 0 =
      ∫ current in (0 : ℝ)..finish, geometricCorrectedPhaseVelocity correction family.patchMotion index current := by
  have derivative (time : ℝ) (member : time ∈ Icc 0 finish) :=
    family.correctedPaperPhase_hasDerivAt_geometric correction phase index (inside time member) (small time member)
      ((correctionSmooth time member).differentiableAt (by norm_num)) (phaseEquation time member)
  have continuous := family.geometricCorrectedPhaseVelocity_continuousOn correction index inside small correctionSmooth
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le finishNonnegative
    (fun time member => (derivative time member).continuousAt.continuousWithinAt)
    (fun time member => derivative time ⟨member.1.le, member.2.le⟩)
    (continuous.intervalIntegrable_of_Icc finishNonnegative)).symm

end EulerNonuniqueness.Paper
