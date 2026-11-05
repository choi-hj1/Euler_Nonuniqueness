import Mathlib

namespace EulerNonuniqueness.General

theorem weighted_inverse_power_triplet_bound
    {receiver source distance clearance hessian : ℝ}
    (receiverPositive : 0 < receiver) (sourcePositive : 0 < source) (distancePositive : 0 < distance)
    (receiverSmall : receiver ≤ 1) (sourceSmall : source ≤ 1)
    (clearanceNonnegative : 0 ≤ clearance)
    (receiverSeparated : receiver ≤ clearance * distance) (sourceSeparated : source ≤ clearance * distance)
    (hessianSmall : hessian ≤ 1) :
    (receiver / source) ^ 4 *
      ((1 / (receiver * distance ^ 3) + 1 / distance ^ 4 + receiver / distance ^ 5) +
        source⁻¹ * (1 / (receiver * distance ^ 2) + 1 / distance ^ 3 + receiver / distance ^ 4) +
        source * (1 / (receiver * distance ^ 4) + 1 / distance ^ 5 + receiver / distance ^ 6) +
        hessian * source * (1 / (receiver * distance ^ 3) + 1 / distance ^ 4 + receiver / distance ^ 5)) ≤
      (clearance ^ 2 + 3 * clearance ^ 3 + 4 * clearance ^ 4 + 3 * clearance ^ 5 + clearance ^ 6) / source ^ 5 := by
  let receiverRatio := receiver / distance
  let sourceRatio := source / distance
  let secondConstant := clearance ^ 3 + clearance ^ 4 + clearance ^ 5
  let firstConstant := clearance ^ 2 + clearance ^ 3 + clearance ^ 4
  let translatedConstant := clearance ^ 4 + clearance ^ 5 + clearance ^ 6
  let secondKernel := 1 / (receiver * distance ^ 3) + 1 / distance ^ 4 + receiver / distance ^ 5
  let firstKernel := source⁻¹ * (1 / (receiver * distance ^ 2) + 1 / distance ^ 3 + receiver / distance ^ 4)
  let translatedKernel := source * (1 / (receiver * distance ^ 4) + 1 / distance ^ 5 + receiver / distance ^ 6)
  have receiverRatioNonnegative : 0 ≤ receiverRatio := div_nonneg receiverPositive.le distancePositive.le
  have sourceRatioNonnegative : 0 ≤ sourceRatio := div_nonneg sourcePositive.le distancePositive.le
  have receiverRatioBound : receiverRatio ≤ clearance := (div_le_iff₀ distancePositive).mpr receiverSeparated
  have sourceRatioBound : sourceRatio ≤ clearance := (div_le_iff₀ distancePositive).mpr sourceSeparated
  have powers (power : ℕ) : receiverRatio ^ power ≤ clearance ^ power :=
    pow_le_pow_left₀ receiverRatioNonnegative receiverRatioBound power
  have secondSum : receiverRatio ^ 3 + receiverRatio ^ 4 + receiverRatio ^ 5 ≤ secondConstant :=
    add_le_add (add_le_add (powers 3) (powers 4)) (powers 5)
  have firstSum : receiverRatio ^ 2 + receiverRatio ^ 3 + receiverRatio ^ 4 ≤ firstConstant :=
    add_le_add (add_le_add (powers 2) (powers 3)) (powers 4)
  have fourthSource : 0 < source ^ 4 := pow_pos sourcePositive _
  have fifthSource : 0 < source ^ 5 := pow_pos sourcePositive _
  have sourcePower : source ^ 5 ≤ source ^ 4 := by
    rw [pow_succ]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left sourceSmall fourthSource.le
  have secondConstantNonnegative : 0 ≤ secondConstant := by dsimp only [secondConstant]; positivity
  have firstConstantNonnegative : 0 ≤ firstConstant := by dsimp only [firstConstant]; positivity
  have translatedConstantNonnegative : 0 ≤ translatedConstant := by dsimp only [translatedConstant]; positivity
  have secondIdentity : (receiver / source) ^ 4 * secondKernel =
      (receiverRatio ^ 3 + receiverRatio ^ 4 + receiverRatio ^ 5) / source ^ 4 := by
    dsimp only [secondKernel, receiverRatio]
    field_simp [receiverPositive.ne', sourcePositive.ne', distancePositive.ne']
    <;> ring
  have secondEstimate : (receiver / source) ^ 4 * secondKernel ≤ secondConstant / source ^ 5 := by
    rw [secondIdentity]
    exact (div_le_div_of_nonneg_right secondSum fourthSource.le).trans
      (div_le_div_of_nonneg_left secondConstantNonnegative fifthSource sourcePower)
  have firstIdentity : (receiver / source) ^ 4 * firstKernel =
      receiver * (receiverRatio ^ 2 + receiverRatio ^ 3 + receiverRatio ^ 4) / source ^ 5 := by
    dsimp only [firstKernel, receiverRatio]
    field_simp [receiverPositive.ne', sourcePositive.ne', distancePositive.ne']
    <;> ring
  have firstEstimate : (receiver / source) ^ 4 * firstKernel ≤ firstConstant / source ^ 5 := by
    rw [firstIdentity]
    apply div_le_div_of_nonneg_right _ fifthSource.le
    exact (mul_le_mul_of_nonneg_left firstSum receiverPositive.le).trans
      (mul_le_of_le_one_left firstConstantNonnegative receiverSmall)
  have translatedIdentity : (receiver / source) ^ 4 * translatedKernel =
      sourceRatio * (receiverRatio ^ 3 + receiverRatio ^ 4 + receiverRatio ^ 5) / source ^ 4 := by
    dsimp only [translatedKernel, sourceRatio, receiverRatio]
    field_simp [receiverPositive.ne', sourcePositive.ne', distancePositive.ne']
    <;> ring
  have translatedSum : sourceRatio * (receiverRatio ^ 3 + receiverRatio ^ 4 + receiverRatio ^ 5) ≤ translatedConstant := by
    apply (mul_le_mul_of_nonneg_left secondSum sourceRatioNonnegative).trans
    apply (mul_le_mul_of_nonneg_right sourceRatioBound secondConstantNonnegative).trans_eq
    dsimp only [secondConstant, translatedConstant]
    ring
  have translatedEstimate : (receiver / source) ^ 4 * translatedKernel ≤ translatedConstant / source ^ 5 := by
    rw [translatedIdentity]
    exact (div_le_div_of_nonneg_right translatedSum fourthSource.le).trans
      (div_le_div_of_nonneg_left translatedConstantNonnegative fifthSource sourcePower)
  have hessianSource : hessian * source ≤ 1 :=
    (mul_le_mul_of_nonneg_right hessianSmall sourcePositive.le).trans (by simpa only [one_mul] using sourceSmall)
  have secondNonnegative : 0 ≤ (receiver / source) ^ 4 * secondKernel := by
    dsimp only [secondKernel]
    positivity
  have hessianEstimate : (receiver / source) ^ 4 * (hessian * source * secondKernel) ≤ secondConstant / source ^ 5 := by
    calc
      _ = (hessian * source) * ((receiver / source) ^ 4 * secondKernel) := by ring
      _ ≤ (receiver / source) ^ 4 * secondKernel := mul_le_of_le_one_left secondNonnegative hessianSource
      _ ≤ _ := secondEstimate
  calc
    _ = (receiver / source) ^ 4 * secondKernel + (receiver / source) ^ 4 * firstKernel +
        (receiver / source) ^ 4 * translatedKernel +
          (receiver / source) ^ 4 * (hessian * source * secondKernel) := by
      dsimp only [secondKernel, firstKernel, translatedKernel]
      ring
    _ ≤ secondConstant / source ^ 5 + firstConstant / source ^ 5 +
        translatedConstant / source ^ 5 + secondConstant / source ^ 5 :=
      add_le_add (add_le_add (add_le_add secondEstimate firstEstimate) translatedEstimate) hessianEstimate
    _ = _ := by dsimp only [secondConstant, firstConstant, translatedConstant]; ring

end EulerNonuniqueness.General
