import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

noncomputable section

namespace EulerNonuniqueness.Section6

theorem signedSourceReceiverGeometry {Space Part : Type*} [SeminormedAddCommGroup Space]
    (ideal first second : Space) (firstPositions secondPositions : Part → Space)
    {gap radius : ℝ} (positive : 0 < gap) (radiusNonnegative : 0 ≤ radius)
    (radiusSmall : radius ≤ gap / 16) (idealNorm : ‖ideal‖ = gap)
    (firstClose : ‖first - ideal‖ ≤ 3 * gap / 16)
    (secondClose : ‖second - ideal‖ ≤ 3 * gap / 16)
    (firstPositionBound : ∀ patch, ‖firstPositions patch‖ ≤ radius)
    (secondPositionBound : ∀ patch, ‖secondPositions patch‖ ≤ radius)
    (patchRadius : Part → ℝ) (patchRadiusSmall : ∀ patch, 2 * patchRadius patch ≤ gap / 16) :
    radius + 3 * gap / 8 + gap / 8 ≤ ‖first‖ ∧
    ‖second - first‖ ≤ 3 * gap / 8 ∧
    (∀ patch, 2 * patchRadius patch + gap / 2 + gap / 8 ≤ ‖first - firstPositions patch‖) ∧
    (∀ patch, 2 * patchRadius patch + gap / 8 ≤ ‖second - secondPositions patch‖) ∧
    (∀ patch, ‖(first - firstPositions patch) - (second - secondPositions patch)‖ ≤ gap / 2) ∧
    (∀ patch, 3 * gap / 4 ≤ ‖second - secondPositions patch‖) := by
  have firstLower : 13 * gap / 16 ≤ ‖first‖ := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub ideal first 0
    simp only [sub_zero, norm_sub_rev ideal first, idealNorm] at triangle
    linarith
  have secondLower : 13 * gap / 16 ≤ ‖second‖ := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub ideal second 0
    simp only [sub_zero, norm_sub_rev ideal second, idealNorm] at triangle
    linarith
  have difference : ‖second - first‖ ≤ 3 * gap / 8 := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub second ideal first
    rw [norm_sub_rev ideal first] at triangle
    linarith
  have firstSourceLower (patch : Part) : 3 * gap / 4 ≤ ‖first - firstPositions patch‖ := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub first (firstPositions patch) 0
    simp only [sub_zero] at triangle
    linarith [firstPositionBound patch]
  have secondSourceLower (patch : Part) : 3 * gap / 4 ≤ ‖second - secondPositions patch‖ := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub second (secondPositions patch) 0
    simp only [sub_zero] at triangle
    linarith [secondPositionBound patch]
  refine ⟨by linarith, difference, ?_, ?_, ?_, secondSourceLower⟩
  · intro patch
    linarith [firstSourceLower patch, patchRadiusSmall patch]
  · intro patch
    linarith [secondSourceLower patch, patchRadiusSmall patch]
  · intro patch
    have identity : (first - firstPositions patch) - (second - secondPositions patch) =
        (first - second) - (firstPositions patch - secondPositions patch) := by abel
    rw [identity]
    have triangle := norm_sub_le (first - second) (firstPositions patch - secondPositions patch)
    have sourceTriangle := norm_sub_le (firstPositions patch) (secondPositions patch)
    rw [norm_sub_rev first second] at triangle
    linarith [firstPositionBound patch, secondPositionBound patch]

end EulerNonuniqueness.Section6
