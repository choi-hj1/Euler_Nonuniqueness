import EulerNonuniqueness.General.FrozenQuadraticCubicRemainderBound

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

local instance scaledBoundOperatorGroup : NormedAddCommGroup (Space →L[ℝ] Space) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := Space) (F := Space) (σ₁₂ := RingHom.id ℝ)
local instance scaledBoundOperatorSpace : NormedSpace ℝ (Space →L[ℝ] Space) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := Space) (F := Space) (σ₁₂ := RingHom.id ℝ)
local instance scaledBoundBilinearGroup : NormedAddCommGroup (BilinearEnd Space) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := Space) (F := Space →L[ℝ] Space) (σ₁₂ := RingHom.id ℝ)
local instance scaledBoundBilinearSpace : NormedSpace ℝ (BilinearEnd Space) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := Space) (F := Space →L[ℝ] Space) (σ₁₂ := RingHom.id ℝ)

theorem norm_scaled_frozen_quadratic_remainder_le
    (quadratic correction : BilinearEnd Space) (frequency : ℝ) (value remainder forcing : Space)
    {cubicBound quadraticBound correctionBound : ℝ}
    (cubicNonnegative : 0 ≤ cubicBound) (quadraticNonnegative : 0 ≤ quadraticBound)
    (correctionNonnegative : 0 ≤ correctionBound)
    (quadraticNorm : ‖quadratic‖ ≤ quadraticBound) (correctionNorm : ‖correction‖ ≤ correctionBound)
    (small : ‖value‖ ≤ 1) (remainderNorm : ‖remainder‖ ≤ cubicBound * ‖value‖ ^ 3) :
    ‖frequency • remainder + forcing -
      (correction ((frequency • quadratic) value value + (frequency • remainder + forcing)) value +
        correction value ((frequency • quadratic) value value + (frequency • remainder + forcing)))‖ ≤
      (|frequency| * (cubicBound + 2 * correctionBound * (quadraticBound + cubicBound))) * ‖value‖ ^ 3 +
        (1 + 2 * correctionBound * ‖value‖) * ‖forcing‖ := by
  have scaledQuadratic : ‖frequency • quadratic‖ ≤ |frequency| * quadraticBound := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left quadraticNorm (abs_nonneg _)
  have scaledRemainder : ‖frequency • remainder‖ ≤ (|frequency| * cubicBound) * ‖value‖ ^ 3 := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left remainderNorm (abs_nonneg _)).trans_eq (by ring)
  have actual := norm_frozen_quadratic_remainder_le (frequency • quadratic) correction value
    (frequency • remainder) forcing (mul_nonneg (abs_nonneg _) cubicNonnegative)
    (mul_nonneg (abs_nonneg _) quadraticNonnegative) correctionNonnegative
    scaledQuadratic correctionNorm small scaledRemainder
  have identity : |frequency| * cubicBound +
      2 * correctionBound * (|frequency| * quadraticBound + |frequency| * cubicBound) =
      |frequency| * (cubicBound + 2 * correctionBound * (quadraticBound + cubicBound)) := by ring
  rw [identity] at actual
  exact actual

end

end EulerNonuniqueness.General
