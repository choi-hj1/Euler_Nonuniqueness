import EulerNonuniqueness.Section1.UniformQuadraticTransportScaleSmallness
import EulerNonuniqueness.Section5.CascadeStatement

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000

theorem Scales.eventually_source_packet_far_remainder_budget (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {separationFactor tolerance : ℝ} (separationPositive : 0 < separationFactor)
    (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ index : ℕ, ∀ distance : ℝ,
    separationFactor * scales.location (index + 1) ≤ distance →
    let changed := {scales with frequency := frequency}
    22528 * changed.circulation (index + 1) * changed.omega (index + 1) ^ 2 * changed.length (index + 1) ^ 3 /
      (Real.pi * distance ^ 5 * (2 * Real.sqrt 2 * changed.omega index)) ≤
      tolerance * (Real.sqrt 3 * changed.circulation (index + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega index ^ 2 * distance ^ 4)) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_omega_sq_length_lt_location ratioBound alphaPositive
      (show 0 < tolerance * separationFactor / 11264 by positivity)]
    with frequency frequencyOne transport index distance distanceLower
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have sourcePositive := changed.omega_pos frequencyPositive ratioPositive (index + 1)
  have receiverPositive := changed.omega_pos frequencyPositive ratioPositive index
  have lengthPositive := changed.length_pos (index + 1)
  have distancePositive : 0 < distance :=
    (mul_pos separationPositive (scales.location_pos (index + 1))).trans_le distanceLower
  have sourceEquation : changed.omega (index + 1) = changed.omega index * changed.ratio := by
    simp only [Scales.omega, pow_succ, mul_assoc]
  have receiverSource : changed.omega index ≤ changed.omega (index + 1) := by
    rw [sourceEquation]
    exact le_mul_of_one_le_right receiverPositive.le (by change 1 ≤ scales.ratio; linarith)
  have frequencyRatio : changed.omega index / changed.omega (index + 1) ≤ 1 :=
    (div_le_one sourcePositive).mpr receiverSource
  have small : 11264 * (changed.omega (index + 1) ^ 2 * changed.length (index + 1) / distance) ≤ tolerance := by
    have reduced : changed.omega (index + 1) ^ 2 * changed.length (index + 1) / distance ≤ tolerance / 11264 := by
      apply (div_le_iff₀ distancePositive).mpr
      have first := (transport (index + 1)).le
      have second := mul_le_mul_of_nonneg_left distanceLower (div_nonneg tolerancePositive.le (by norm_num : (0 : ℝ) ≤ 11264))
      have comparison : (tolerance * separationFactor / 11264) * scales.location (index + 1) ≤
          tolerance / 11264 * distance := by
        convert second using 1 <;> ring
      exact first.trans comparison
    linarith
  let common := changed.circulation (index + 1) ^ 2 /
    (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega index ^ 2 * distance ^ 4)
  have commonNonnegative : 0 ≤ common := by dsimp only [common]; positivity
  have identity :
      22528 * changed.circulation (index + 1) * changed.omega (index + 1) ^ 2 * changed.length (index + 1) ^ 3 /
        (Real.pi * distance ^ 5 * (2 * Real.sqrt 2 * changed.omega index)) =
      (11264 * (changed.omega (index + 1) ^ 2 * changed.length (index + 1) / distance)) *
        (changed.omega index / changed.omega (index + 1)) * common := by
    dsimp only [common]
    rw [Scales.circulation]
    field_simp [sourcePositive.ne', receiverPositive.ne', lengthPositive.ne', distancePositive.ne', Real.pi_ne_zero,
      ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))]
    <;> ring
  dsimp only
  rw [identity]
  have coefficient := mul_le_mul small frequencyRatio
    (div_nonneg receiverPositive.le sourcePositive.le) tolerancePositive.le
  simp only [mul_one] at coefficient
  have sqrtThree : 1 ≤ Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have bound := mul_le_mul_of_nonneg_right coefficient commonNonnegative
  have enlarged := mul_le_mul_of_nonneg_left sqrtThree (mul_nonneg tolerancePositive.le commonNonnegative)
  exact bound.trans (by
    convert enlarged using 1 <;> dsimp only [common] <;> ring)

end EulerNonuniqueness.Paper
