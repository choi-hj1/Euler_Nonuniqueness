import EulerNonuniqueness.Section5.CascadeFinitePassageGap

noncomputable section

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem normalizedSeparatingOrbit_exists_cascade_gap_factor
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit) :
    ∃ factor > (0 : ℝ), factor ≤ 1 / 8 ∧ ∀ time : ℝ, ∀ target source : Fin 4, source ≠ target →
      2 * factor ≤ ‖centrallySymmetricFourPoint (orbit.positive time) (-orbit.negative time) target -
        centrallySymmetricFourPoint (orbit.positive time) (-orbit.negative time) source‖ := by
  obtain ⟨gap, gapPositive, separated⟩ := normalizedSeparatingOrbit_uniform_pair_gap orbit normalized
  refine ⟨min (gap / 4) (1 / 8), lt_min (by positivity) (by norm_num), min_le_right _ _, ?_⟩
  intro time target source different
  have bound := separated time target source different.symm
  have small := min_le_left (gap / 4) (1 / 8)
  linarith

theorem cascadeNormalizedPointPositions_pair_norm {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (index : Fin count) (start time : ℝ)
    {rotation : ℂ} (rotationNorm : ‖rotation‖ = 1) (target source : Fin 4) :
    ‖cascadeNormalizedPointPositions scales motion index start rotation time target -
      cascadeNormalizedPointPositions scales motion index start rotation time source‖ =
      ‖patchCentroid motion (start + time / scales.omega (index.val + 1)) index target -
        patchCentroid motion (start + time / scales.omega (index.val + 1)) index source‖ /
        scales.length (index.val + 1) := by
  have positive := scales.length_pos (index.val + 1)
  simp only [cascadeNormalizedPointPositions, ← mul_sub, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive, rotationNorm, mul_one,
    fourPointCenterProjection]
  have identity (first second center : ℂ) : (first - center) - (second - center) = first - second := by abel
  rw [identity]
  ring

theorem cascadeNormalizedPointPositions_strict_gap_physical {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (index : Fin count) (start time : ℝ)
    {rotation : ℂ} (rotationNorm : ‖rotation‖ = 1) {factor : ℝ}
    (actualGap : ∀ target source : Fin 4, source ≠ target →
      factor < ‖cascadeNormalizedPointPositions scales motion index start rotation time target -
        cascadeNormalizedPointPositions scales motion index start rotation time source‖) :
    ∀ target source : Fin 4, source ≠ target → factor * scales.length (index.val + 1) <
      ‖patchCentroid motion (start + time / scales.omega (index.val + 1)) index target -
        patchCentroid motion (start + time / scales.omega (index.val + 1)) index source‖ := by
  intro target source different
  have actual := actualGap target source different
  rw [cascadeNormalizedPointPositions_pair_norm scales motion index start time rotationNorm] at actual
  exact (lt_div_iff₀ (scales.length_pos _)).mp actual

end EulerNonuniqueness.Paper
