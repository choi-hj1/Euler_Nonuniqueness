import EulerNonuniqueness.Section1.MacroscopicMultipoleRow

noncomputable section

namespace EulerNonuniqueness.Paper

theorem Scales.macroscopicMultipoleInteractionKernel_coefficient_lower_bound (scales : Scales)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {hessian : ℝ} (hessianNonnegative : 0 ≤ hessian) {receiver source : ℕ} (different : receiver ≠ source) :
    let receiverScale := scales.location receiver
    let sourceScale := scales.location source
    let distance := |receiverScale - sourceScale| / 8
    scales.circulation source *
      (sourceScale / distance ^ 3 + sourceScale ^ 2 / distance ^ 4 + sourceScale ^ 3 / distance ^ 5) ≤
      24 * scales.macroscopicMultipoleInteractionKernel hessian receiver source := by
  dsimp only
  let receiverScale := scales.location receiver
  let sourceScale := scales.location source
  let distance := |receiverScale - sourceScale| / 8
  change scales.circulation source *
    (sourceScale / distance ^ 3 + sourceScale ^ 2 / distance ^ 4 + sourceScale ^ 3 / distance ^ 5) ≤ _
  have receiverPositive : 0 < receiverScale := scales.location_pos receiver
  have distancePositive : 0 < distance := div_pos (scales.location_distance_pos different) (by norm_num)
  have geometry := scales.location_sum_le_three_distance different
  have receiverBound : receiverScale ≤ 24 * distance := by
    dsimp only [receiverScale, sourceScale, distance]
    linarith [scales.location_pos source]
  have ratioBound : receiverScale / distance ≤ 24 := (div_le_iff₀ distancePositive).mpr receiverBound
  have lower := scales.macroscopicMultipoleInteractionKernel_velocity_lower_bound frequencyPositive ratioPositive hessianNonnegative different
  change scales.circulation source * (sourceScale / (receiverScale * distance ^ 2) +
    sourceScale ^ 2 / (receiverScale * distance ^ 3) + sourceScale ^ 3 / (receiverScale * distance ^ 4)) ≤ _ at lower
  have multiplied := mul_le_mul_of_nonneg_left lower (show 0 ≤ receiverScale / distance by positivity)
  have enlarged := mul_le_mul_of_nonneg_right ratioBound
    (scales.macroscopicMultipoleInteractionKernel_nonnegative frequencyPositive ratioPositive hessianNonnegative receiver source)
  apply le_trans _ enlarged
  convert multiplied using 1 <;> field_simp [receiverPositive.ne', distancePositive.ne'] <;> ring

theorem Scales.coefficient_receiver_coarse_bound (scales : Scales)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {receiver source : ℕ} (different : receiver ≠ source) :
    let receiverScale := scales.location receiver
    let sourceScale := scales.location source
    let distance := |receiverScale - sourceScale| / 8
    scales.circulation source *
      (256 * receiverScale * sourceScale / distance ^ 4 +
        4096 * receiverScale * sourceScale ^ 2 / distance ^ 5) ≤
      60000000 * scales.circulation source / distance ^ 2 := by
  dsimp only
  let receiverScale := scales.location receiver
  let sourceScale := scales.location source
  let distance := |receiverScale - sourceScale| / 8
  change scales.circulation source * (256 * receiverScale * sourceScale / distance ^ 4 +
    4096 * receiverScale * sourceScale ^ 2 / distance ^ 5) ≤ 60000000 * scales.circulation source / distance ^ 2
  have receiverPositive : 0 < receiverScale := scales.location_pos receiver
  have sourcePositive : 0 < sourceScale := scales.location_pos source
  have distancePositive : 0 < distance := div_pos (scales.location_distance_pos different) (by norm_num)
  have geometry := scales.location_sum_le_three_distance different
  have receiverBound : receiverScale / distance ≤ 24 := (div_le_iff₀ distancePositive).mpr (by
    dsimp only [receiverScale, sourceScale, distance]; linarith)
  have sourceBound : sourceScale / distance ≤ 24 := (div_le_iff₀ distancePositive).mpr (by
    dsimp only [receiverScale, sourceScale, distance]; linarith)
  have receiverNonnegative : 0 ≤ receiverScale / distance := by positivity
  have sourceNonnegative : 0 ≤ sourceScale / distance := by positivity
  have squareBound := pow_le_pow_left₀ sourceNonnegative sourceBound 2
  have productBound := mul_le_mul receiverBound sourceBound sourceNonnegative (by norm_num : (0 : ℝ) ≤ 24)
  have cubicBound := mul_le_mul receiverBound squareBound (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 24)
  have scalar : 256 * (receiverScale / distance) * (sourceScale / distance) +
      4096 * (receiverScale / distance) * (sourceScale / distance) ^ 2 ≤ 60000000 := by nlinarith
  have actual := mul_le_mul_of_nonneg_left scalar
    (show 0 ≤ scales.circulation source / distance ^ 2 from div_nonneg
      (scales.circulation_pos frequencyPositive ratioPositive source).le (sq_nonneg _))
  convert actual using 1 <;> field_simp [distancePositive.ne'] <;> ring

end EulerNonuniqueness.Paper
