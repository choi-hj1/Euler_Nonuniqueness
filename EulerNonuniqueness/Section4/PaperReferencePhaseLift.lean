import EulerNonuniqueness.Section6.PaperCentroidEndpoints
import EulerNonuniqueness.General.ComplexPhaseWithin
import EulerNonuniqueness.Section4.ReferencePhaseLiftUniqueness
import EulerNonuniqueness.Section4.ReferenceConstructedPhaseLift

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000

def referencePositiveDiagonalVelocity {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) : ℂ :=
  (patchAverageVelocity scales motion time index 0 (biotSavart (patchVorticity scales motion time)) -
    patchAverageVelocity scales motion time index 1 (biotSavart (patchVorticity scales motion time))) / 2

theorem FinitePatchEvolution.exists_reference_phaseLift_of_boundary_gaps
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
      scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference motion current index) :
    ∃ phaseLift : ℝ → Fin count → ℝ, ReferencePhaseLift motion phase phaseLift ∧
      ∀ index, ∀ time ∈ Icc (0 : ℝ) 2, HasDerivAt (fun current => phaseLift current index)
        (referencePositiveDiagonalVelocity scales motion time index / positiveHalfDiagonal motion time index).im time := by
  have data (index : Fin count) (patch : Fin 4) := evolution.patchCentroid_closed_derivative_of_boundary_gaps
    (by norm_num : (0 : ℝ) < 2) amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index patch
  have equation (index : Fin count) (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) :
      HasDerivWithinAt (fun current => positiveHalfDiagonal motion current index)
        (referencePositiveDiagonalVelocity scales motion time index) (Icc (0 : ℝ) 2) time :=
    ((data index 0).2.2 time member).sub ((data index 1).2.2 time member) |>.div_const 2
  have velocityContinuous (index : Fin count) :
      ContinuousOn (fun current => referencePositiveDiagonalVelocity scales motion current index) (Icc (0 : ℝ) 2) := by
    exact ((data index 0).2.1.sub (data index 1).2.1).div continuousOn_const (fun _ _ => by norm_num)
  have nonzero (index : Fin count) (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) :
      positiveHalfDiagonal motion time index ≠ 0 := by
    intro zero
    have lower := differenceLower time member index
    dsimp only [diagonalDifference] at lower
    rw [zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_sub] at lower
    nlinarith only [lower, sq_pos_of_pos (scales.length_pos (index.val + 1)), sq_nonneg ‖negativeHalfDiagonal motion time index‖]
  have lifts (index : Fin count) : ∃ lift : ℝ → ℝ, Continuous lift ∧ lift 0 = phase index ∧
      ∀ time ∈ Icc (0 : ℝ) 2, HasDerivAt lift
        (referencePositiveDiagonalVelocity scales motion time index / positiveHalfDiagonal motion time index).im time ∧
          positiveHalfDiagonal motion time index = (‖positiveHalfDiagonal motion time index‖ : ℂ) *
            Complex.exp (Complex.I * (lift time : ℂ)) := by
    apply General.exists_complex_phase_on_Icc_of_within_derivative (by norm_num : (0 : ℝ) ≤ 2)
      (equation index) (velocityContinuous index) (nonzero index)
    rw [(evolution.reference_initial_diagonals (by norm_num : (0 : ℝ) ≤ 2) amplitudePositive frequencyPositive ratioPositive initial index).1]
    exact initialPositiveDiagonal_polar scales _ _ _
  choose lift continuous initialValue properties using lifts
  refine ⟨fun time index => lift index time, ?_, ?_⟩
  · intro index
    exact ⟨(continuous index).continuousOn, initialValue index, fun time member => (properties index time member).2⟩
  · intro index time member
    exact (properties index time member).1

end EulerNonuniqueness.Paper
