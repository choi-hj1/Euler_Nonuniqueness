import EulerNonuniqueness.Section4.PaperReferencePhaseLift

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.referencePhaseLift_hasDerivWithinAt_of_boundary_gaps
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {threshold : ℝ}
    (evolution : FinitePatchEvolution scales motion 2)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (radiusPositive : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
    (control : ∀ current ∈ Icc (0 : ℝ) 2, ∀ index patch,
      ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle scales motion current index patch bound)
    (separated : ∀ current ∈ Icc (0 : ℝ) 2, ∀ (index other : Fin count) (patch otherPatch : Fin 4),
      (other, otherPatch) ≠ (index, patch) →
      8 * scales.radius (index.val + 1) + 8 * scales.radius (other.val + 1) <
        dist (motion.boundary current index patch 0) (motion.boundary current other otherPatch 0))
    {phase unstable : Fin count → ℝ} (initial : ReferenceInitialDisks scales motion phase unstable threshold)
    (differenceLower : ∀ current ∈ Icc (0 : ℝ) 2, ∀ index : Fin count,
      scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference motion current index)
    {given : ℝ → Fin count → ℝ} (givenLift : ReferencePhaseLift motion phase given) :
    ∀ index, ∀ time ∈ Icc (0 : ℝ) 2, HasDerivWithinAt (fun current => given current index)
      (referencePositiveDiagonalVelocity scales motion time index / positiveHalfDiagonal motion time index).im
        (Icc (0 : ℝ) 2) time := by
  obtain ⟨chosen, chosenLift, chosenEquation⟩ := evolution.exists_reference_phaseLift_of_boundary_gaps
    amplitudePositive frequencyPositive ratioPositive radiusPositive control separated initial differenceLower
  have nonzero (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (index : Fin count) :
      positiveHalfDiagonal motion time index ≠ 0 := by
    intro zero
    have lower := differenceLower time member index
    dsimp only [diagonalDifference] at lower
    rw [zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_sub] at lower
    nlinarith only [lower, sq_pos_of_pos (scales.length_pos (index.val + 1)), sq_nonneg ‖negativeHalfDiagonal motion time index‖]
  have agreement := givenLift.eqOn_of_nonzero chosenLift nonzero
  intro index time member
  exact (chosenEquation index time member).hasDerivWithinAt.congr_of_mem (agreement index) member

end EulerNonuniqueness.Paper

