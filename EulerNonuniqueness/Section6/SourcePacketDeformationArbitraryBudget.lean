import EulerNonuniqueness.Section6.SourcePacketFineDeformationBudget

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000

theorem Scales.eventually_source_packet_deformation_arbitrary_budget (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    {scaleRoot boundaryConstant constant tolerance : ℝ} (rootPositive : 0 < scaleRoot)
    (boundaryNonnegative : 0 ≤ boundaryConstant) (constantNonnegative : 0 ≤ constant)
    (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ, ∀ distance : ℝ, 0 < distance →
    let changed := {scales with frequency := frequency}
    let deformation := boundaryConstant / (scaleRoot ^ 2 * changed.omega (index + 1) ^ 2)
    constant * changed.circulation (index + 1) * changed.radius (index + 1) ^ 2 * deformation /
      (Real.pi * distance ^ 4 * (2 * Real.sqrt 2 * changed.omega index)) ≤
      tolerance * (Real.sqrt 3 * changed.circulation (index + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega index ^ 2 * distance ^ 4)) := by
  have constantPositive : 0 < constant + 1 := by linarith
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_source_packet_fine_deformation_budget amplitudePositive ratioBound rootPositive boundaryNonnegative
      (show 0 < tolerance / (constant + 1) by positivity)] with frequency frequencyOne fine index distance distancePositive
  let changed : Scales := {scales with frequency := frequency}
  let deformation := boundaryConstant / (scaleRoot ^ 2 * changed.omega (index + 1) ^ 2)
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have sourcePositive := changed.omega_pos frequencyPositive ratioPositive (index + 1)
  have receiverPositive := changed.omega_pos frequencyPositive ratioPositive index
  have lengthPositive := changed.length_pos (index + 1)
  have circulationPositive := changed.circulation_pos frequencyPositive ratioPositive (index + 1)
  have deformationNonnegative : 0 ≤ deformation := by dsimp only [deformation]; positivity
  have omegaNext : changed.omega (index + 1) = changed.omega index * changed.ratio := by
    simp only [Scales.omega, pow_succ, mul_assoc]
  have receiverSource : changed.omega index ≤ changed.omega (index + 1) := by
    rw [omegaNext]
    exact le_mul_of_one_le_right receiverPositive.le (by change 1 ≤ scales.ratio; linarith)
  have ratioSmall : changed.omega index / changed.omega (index + 1) ≤ 1 := (div_le_one sourcePositive).mpr receiverSource
  have deformationSmall : changed.radius (index + 1) ^ 2 * deformation / changed.length (index + 1) ^ 2 ≤
      tolerance / (constant + 1) := by
    apply (div_le_iff₀ (sq_pos_of_pos lengthPositive)).mpr
    exact fine (index + 1)
  have ratioNonnegative : 0 ≤ changed.omega index / changed.omega (index + 1) := by positivity
  have deformationRatioNonnegative : 0 ≤ changed.radius (index + 1) ^ 2 * deformation / changed.length (index + 1) ^ 2 := by positivity
  have coefficient : (constant / 2) * (changed.omega index / changed.omega (index + 1)) *
      (changed.radius (index + 1) ^ 2 * deformation / changed.length (index + 1) ^ 2) ≤ tolerance := by
    have first := mul_le_mul_of_nonneg_left ratioSmall (show 0 ≤ constant / 2 by positivity)
    simp only [mul_one] at first
    have second := mul_le_mul first deformationSmall deformationRatioNonnegative (show 0 ≤ constant / 2 by positivity)
    have third := mul_le_mul_of_nonneg_right (show constant / 2 ≤ constant + 1 by linarith)
      (show 0 ≤ tolerance / (constant + 1) by positivity)
    have last : (constant + 1) * (tolerance / (constant + 1)) = tolerance := by field_simp <;> ring
    exact second.trans (third.trans_eq last)
  let common := changed.circulation (index + 1) ^ 2 /
    (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega index ^ 2 * distance ^ 4)
  have commonNonnegative : 0 ≤ common := by dsimp only [common]; positivity
  have identity : constant * changed.circulation (index + 1) * changed.radius (index + 1) ^ 2 * deformation /
      (Real.pi * distance ^ 4 * (2 * Real.sqrt 2 * changed.omega index)) =
      ((constant / 2) * (changed.omega index / changed.omega (index + 1)) *
        (changed.radius (index + 1) ^ 2 * deformation / changed.length (index + 1) ^ 2)) * common := by
    dsimp only [common]
    rw [Scales.circulation]
    field_simp [sourcePositive.ne', receiverPositive.ne', lengthPositive.ne', distancePositive.ne', Real.pi_ne_zero,
      ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))]
    <;> ring
  dsimp only
  rw [identity]
  have bound := mul_le_mul_of_nonneg_right coefficient commonNonnegative
  have sqrtThree : 1 ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have enlarged := mul_le_mul_of_nonneg_left sqrtThree (mul_nonneg tolerancePositive.le commonNonnegative)
  exact bound.trans (by convert enlarged using 1 <;> dsimp only [common] <;> ring)

end EulerNonuniqueness.Paper
