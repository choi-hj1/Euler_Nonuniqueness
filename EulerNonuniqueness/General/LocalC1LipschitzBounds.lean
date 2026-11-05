import EulerNonuniqueness.Section3.LocalDerivativeLipschitzCalculus
import EulerNonuniqueness.General.LocalLipschitzCenteredBounds

noncomputable section

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Domain Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem HasLipschitzDerivativeNear.exists_uniform_derivative_ball
    {function : Domain → Target} {center : Domain}
    (regular : HasLipschitzDerivativeNear function center) :
    ∃ radius > 0, ∃ constant ≥ 1,
      (∀ point, ‖point - center‖ ≤ radius → DifferentiableAt ℝ function point) ∧
      (∀ point, ‖point - center‖ ≤ radius → ‖fderiv ℝ function point‖ ≤ constant) ∧
      ∀ first second, ‖first - center‖ ≤ radius → ‖second - center‖ ≤ radius →
        ‖fderiv ℝ function first - fderiv ℝ function second‖ ≤ constant * ‖first - second‖ := by
  obtain ⟨derivativeRadius, derivativePositive, derivativeContained⟩ := Metric.mem_nhds_iff.mp regular.1
  obtain ⟨differenceRadius, differencePositive, differenceConstant, differenceOne, difference⟩ :=
    regular.2.exists_centered_closedBall_difference_bound
  let radius := min 1 (min (derivativeRadius / 2) differenceRadius)
  let constant := differenceConstant + ‖fderiv ℝ function center‖ + 1
  have positive : 0 < radius := lt_min zero_lt_one (lt_min (by positivity) differencePositive)
  have constantOne : 1 ≤ constant := by
    dsimp [constant]
    linarith [norm_nonneg (fderiv ℝ function center)]
  have constantLarge : differenceConstant ≤ constant := by
    dsimp [constant]
    linarith [norm_nonneg (fderiv ℝ function center)]
  have radiusOne : radius ≤ 1 := min_le_left _ _
  have radiusDifference : radius ≤ differenceRadius := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨radius, positive, constant, constantOne, ?_, ?_, ?_⟩
  · intro point small
    apply derivativeContained
    rw [mem_ball, dist_eq_norm]
    exact small.trans_lt ((min_le_right _ _).trans (min_le_left _ _) |>.trans_lt (by linarith))
  · intro point small
    have differenceBound := difference point center (small.trans radiusDifference)
      (by simpa only [sub_self, norm_zero] using differencePositive.le)
    calc
      ‖fderiv ℝ function point‖ ≤
          ‖fderiv ℝ function point - fderiv ℝ function center‖ + ‖fderiv ℝ function center‖ :=
        by
          calc
            _ = ‖(fderiv ℝ function point - fderiv ℝ function center) + fderiv ℝ function center‖ :=
              by rw [sub_add_cancel]
            _ ≤ _ := norm_add_le _ _
      _ ≤ differenceConstant * 1 + ‖fderiv ℝ function center‖ :=
        add_le_add_right (differenceBound.trans
          (mul_le_mul_of_nonneg_left (small.trans radiusOne) (by linarith))) _
      _ ≤ constant := by dsimp [constant]; linarith
  · intro first second firstSmall secondSmall
    exact (difference first second (firstSmall.trans radiusDifference) (secondSmall.trans radiusDifference)).trans
      (mul_le_mul_of_nonneg_right constantLarge (norm_nonneg _))

end EulerNonuniqueness.General
