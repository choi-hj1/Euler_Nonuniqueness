import EulerNonuniqueness.General.RealifiedComplexOperatorDifference
import EulerNonuniqueness.General.LocalLipschitzCenteredBounds

noncomputable section

namespace EulerNonuniqueness.General

variable {Domain ComplexSpace RealSpace : Type*}
  [NormedAddCommGroup Domain]
  [NormedAddCommGroup ComplexSpace] [NormedSpace ℂ ComplexSpace] [NormedSpace ℝ ComplexSpace]
  [IsScalarTower ℝ ℂ ComplexSpace]
  [NormedAddCommGroup RealSpace] [NormedSpace ℝ RealSpace]

theorem exists_realifiedComplexOperator_uniform_local_bounds
    (output : ComplexSpace →L[ℝ] RealSpace) (input : RealSpace →L[ℝ] ComplexSpace)
    (family : Domain → ComplexSpace →L[ℂ] ComplexSpace) (center : Domain)
    (regular : LipschitzNear family center)
    (outputBound : ‖output‖ ≤ 2) (inputBound : ‖input‖ ≤ 1) :
    ∃ radius > 0, ∃ constant ≥ 1,
      (∀ point, ‖point - center‖ ≤ radius → ∀ coefficient : ℂ,
        ‖realifiedComplexOperator output input (family point) coefficient‖ ≤ constant * ‖coefficient‖) ∧
      ∀ first second, ‖first - center‖ ≤ radius → ‖second - center‖ ≤ radius → ∀ coefficient : ℂ,
        ‖realifiedComplexOperator output input (family first) coefficient -
          realifiedComplexOperator output input (family second) coefficient‖ ≤
          constant * ‖coefficient‖ * ‖first - second‖ := by
  obtain ⟨outerRadius, outerPositive, lipschitzConstant, lipschitzOne, difference⟩ :=
    regular.exists_centered_closedBall_difference_bound
  let radius := min 1 outerRadius
  let bound := ‖family center‖ + lipschitzConstant
  let constant := 2 * bound + 2 * lipschitzConstant + 1
  have positive : 0 < radius := lt_min zero_lt_one outerPositive
  have radiusOuter : radius ≤ outerRadius := min_le_right _ _
  have radiusOne : radius ≤ 1 := min_le_left _ _
  have boundNonnegative : 0 ≤ bound := by dsimp [bound]; linarith [norm_nonneg (family center)]
  have constantOne : 1 ≤ constant := by dsimp [constant]; linarith
  have twiceBound : 2 * bound ≤ constant := by dsimp [constant]; linarith
  have twiceLipschitz : 2 * lipschitzConstant ≤ constant := by dsimp [constant]; linarith
  have familyBound (point : Domain) (small : ‖point - center‖ ≤ radius) : ‖family point‖ ≤ bound := by
    have actual := difference point center (small.trans radiusOuter)
      (by simpa only [sub_self, norm_zero] using outerPositive.le)
    calc
      _ = ‖(family point - family center) + family center‖ := by rw [sub_add_cancel]
      _ ≤ ‖family point - family center‖ + ‖family center‖ := norm_add_le _ _
      _ ≤ lipschitzConstant * 1 + ‖family center‖ :=
        add_le_add_right (actual.trans
          (mul_le_mul_of_nonneg_left (small.trans radiusOne) (by linarith))) _
      _ = bound := by dsimp [bound]; ring
  refine ⟨radius, positive, constant, constantOne, ?_, ?_⟩
  · intro point small coefficient
    calc
      _ ≤ 2 * ‖coefficient‖ * ‖family point‖ :=
        realifiedComplexOperator_norm_le_twice output input _ coefficient outputBound inputBound
      _ ≤ 2 * ‖coefficient‖ * bound :=
        mul_le_mul_of_nonneg_left (familyBound point small) (by positivity)
      _ ≤ constant * ‖coefficient‖ := by nlinarith [norm_nonneg coefficient]
  · intro first second firstSmall secondSmall coefficient
    calc
      _ ≤ 2 * ‖coefficient‖ * ‖family first - family second‖ :=
        realifiedComplexOperator_difference_bound output input _ _ coefficient outputBound inputBound
      _ ≤ 2 * ‖coefficient‖ * (lipschitzConstant * ‖first - second‖) :=
        mul_le_mul_of_nonneg_left
          (difference first second (firstSmall.trans radiusOuter) (secondSmall.trans radiusOuter)) (by positivity)
      _ ≤ constant * ‖coefficient‖ * ‖first - second‖ := by
        have scaled := mul_le_mul_of_nonneg_right twiceLipschitz
          (mul_nonneg (norm_nonneg coefficient) (norm_nonneg (first - second)))
        convert scaled using 1 <;> ring

end EulerNonuniqueness.General
