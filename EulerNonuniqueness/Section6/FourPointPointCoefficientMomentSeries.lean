import EulerNonuniqueness.Section6.PointSourceRelativeSeries

noncomputable section

namespace EulerNonuniqueness.Section6

theorem fourPoint_pointSourceTaylorCoefficient_moment_summable_and_tsum_le
    (positions : FourPointConfiguration) (displacement : ℂ) (circulation : ℝ)
    {receiverRadius radius distance weight : ℝ}
    (receiverNonnegative : 0 ≤ receiverRadius) (radiusNonnegative : 0 ≤ radius)
    (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (separated : radius + distance ≤ ‖displacement‖)
    (bounded : ∀ patch, ‖positions patch‖ ≤ radius)
    (small : 4 * weight * receiverRadius / distance < 1) :
    Summable (fun power : ℕ => weight ^ (power + 1) *
      ‖pointSourceTaylorCoefficient circulation receiverRadius positions displacement power‖) ∧
    (∑' power : ℕ, weight ^ (power + 1) *
      ‖pointSourceTaylorCoefficient circulation receiverRadius positions displacement power‖) ≤
      (weight * (|circulation| / (2 * Real.pi)) *
        (4 * distance⁻¹ ^ 3 * ‖fourPointSignedMoment positions‖ +
          128 * distance⁻¹ ^ 4 * radius ^ 2)) *
        (1 - 4 * weight * receiverRadius / distance)⁻¹ := by
  have zeroCoefficient (power : ℕ) :
      pointSourceTaylorCoefficient circulation receiverRadius (fun _ => 0) displacement power = 0 := by
    simp [pointSourceTaylorCoefficient, fourPointSign, Fin.sum_univ_succ]
  have zeroMoment : fourPointSignedMoment (fun _ => 0) = 0 := by
    simp [fourPointSignedMoment]
  have sumBound : (∑ patch : Fin 4, ‖positions patch‖) ≤ 4 * radius := by
    calc
      _ ≤ ∑ _patch : Fin 4, radius := Finset.sum_le_sum (fun patch _ => bounded patch)
      _ = _ := by simp
  have actual := pointSourceTaylorCoefficient_relative_summable_and_tsum_le positions (fun _ => 0)
    displacement circulation receiverNonnegative radiusNonnegative positive weightNonnegative separated bounded
    (fun _ => by simpa using radiusNonnegative) small
  simp only [zeroCoefficient, zeroMoment, sub_zero] at actual
  refine ⟨actual.1, actual.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (sub_nonneg.mpr small.le))
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add_left
  have comparison := mul_le_mul_of_nonneg_left sumBound
    (show 0 ≤ 32 * distance⁻¹ ^ 4 * radius by positivity)
  exact comparison.trans_eq (by ring)

end EulerNonuniqueness.Section6
