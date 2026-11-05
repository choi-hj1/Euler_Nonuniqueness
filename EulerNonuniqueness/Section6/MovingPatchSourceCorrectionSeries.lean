import EulerNonuniqueness.Section6.MovingPatchSourceCentroidCorrection

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper.MovingMaterialPatch

set_option maxHeartbeats 1000000

theorem sourceTaylorCentroidCorrection_receiver_weighted_term_le (path : MovingMaterialPatch)
    (density : ℝ) (anchor first second : ℂ) (power : ℕ) (time : ℝ)
    {receiverRadius travel distance weight : ℝ} (receiverNonnegative : 0 ≤ receiverRadius)
    (travelNonnegative : 0 ≤ travel) (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (centered : path.center time = path.centroid time)
    (area : volume.real (path.domain time) = Real.pi * path.radius ^ 2)
    (separated : 2 * path.radius + travel + distance ≤ ‖anchor - path.center time‖)
    (firstBound : ‖first - anchor‖ ≤ travel) (secondBound : ‖second - anchor‖ ≤ travel) :
    weight ^ (power + 1) *
      ‖path.sourceTaylorCentroidCorrection density first receiverRadius power time -
        path.sourceTaylorCentroidCorrection density second receiverRadius power time‖ ≤
      (1024 * weight * |density| * path.radius ^ 4 * distance⁻¹ ^ 5 * ‖first - second‖) *
        (8 * weight * receiverRadius / distance) ^ power := by
  have firstDegree : (power + 2 : ℝ) ≤ 4 * (2 : ℝ) ^ power := by
    have bound : (power + 2 : ℝ) ≤ (2 : ℝ) ^ (power + 2) := by
      exact_mod_cast (Nat.lt_two_pow_self (n := power + 2)).le
    simpa only [pow_add, show (2 : ℝ) ^ 2 = 4 by norm_num, mul_comm] using bound
  have secondDegree : (power + 3 : ℝ) ≤ 8 * (2 : ℝ) ^ power := by
    have bound : (power + 3 : ℝ) ≤ (2 : ℝ) ^ (power + 3) := by
      exact_mod_cast (Nat.lt_two_pow_self (n := power + 3)).le
    simpa only [pow_add, show (2 : ℝ) ^ 3 = 8 by norm_num, mul_comm] using bound
  have thirdDegree : (power + 4 : ℝ) ≤ 16 * (2 : ℝ) ^ power := by
    have bound : (power + 4 : ℝ) ≤ (2 : ℝ) ^ (power + 4) := by
      exact_mod_cast (Nat.lt_two_pow_self (n := power + 4)).le
    simpa only [pow_add, show (2 : ℝ) ^ 4 = 16 by norm_num, mul_comm] using bound
  have degreeBound : (power + 2 : ℝ) * (power + 3 : ℝ) * (power + 4 : ℝ) ≤ 512 * (8 : ℝ) ^ power := by
    apply (mul_le_mul (mul_le_mul firstDegree secondDegree (by positivity) (by positivity))
      thirdDegree (by positivity) (by positivity)).trans_eq
    rw [show (8 : ℝ) = 2 * 2 * 2 by norm_num, mul_pow, mul_pow]
    ring
  have actual := mul_le_mul_of_nonneg_left
    (path.sourceTaylorCentroidCorrection_receiver_difference_norm_le density anchor first second power time
      receiverNonnegative travelNonnegative positive centered area separated firstBound secondBound)
    (pow_nonneg weightNonnegative (power + 1))
  apply actual.trans
  calc
    _ ≤ weight ^ (power + 1) * ((2 * |density| * path.radius ^ 4) * (receiverRadius / distance) ^ power *
        ((512 * (8 : ℝ) ^ power) * distance⁻¹ ^ 5) * ‖first - second‖) := by
      gcongr
    _ = _ := by simp only [pow_succ, mul_pow, div_pow]; ring

theorem sourceTaylorCentroidCorrection_receiver_summable_and_tsum_le (path : MovingMaterialPatch)
    (density : ℝ) (anchor first second : ℂ) (time : ℝ)
    {receiverRadius travel distance weight : ℝ} (receiverNonnegative : 0 ≤ receiverRadius)
    (travelNonnegative : 0 ≤ travel) (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (centered : path.center time = path.centroid time)
    (area : volume.real (path.domain time) = Real.pi * path.radius ^ 2)
    (separated : 2 * path.radius + travel + distance ≤ ‖anchor - path.center time‖)
    (firstBound : ‖first - anchor‖ ≤ travel) (secondBound : ‖second - anchor‖ ≤ travel)
    (small : 8 * weight * receiverRadius / distance < 1) :
    Summable (fun power : ℕ => weight ^ (power + 1) *
      ‖path.sourceTaylorCentroidCorrection density first receiverRadius power time -
        path.sourceTaylorCentroidCorrection density second receiverRadius power time‖) ∧
    (∑' power : ℕ, weight ^ (power + 1) *
      ‖path.sourceTaylorCentroidCorrection density first receiverRadius power time -
        path.sourceTaylorCentroidCorrection density second receiverRadius power time‖) ≤
      (1024 * weight * |density| * path.radius ^ 4 * distance⁻¹ ^ 5 * ‖first - second‖) *
        (1 - 8 * weight * receiverRadius / distance)⁻¹ := by
  have ratioNonnegative : 0 ≤ 8 * weight * receiverRadius / distance := by positivity
  have geometric := (summable_geometric_of_lt_one ratioNonnegative small).mul_left
    (1024 * weight * |density| * path.radius ^ 4 * distance⁻¹ ^ 5 * ‖first - second‖)
  have bound (power : ℕ) := path.sourceTaylorCentroidCorrection_receiver_weighted_term_le density anchor first second
    power time receiverNonnegative travelNonnegative positive weightNonnegative centered area separated firstBound secondBound
  have summable := Summable.of_nonneg_of_le (fun power => by positivity) bound geometric
  refine ⟨summable, ?_⟩
  simpa only [tsum_mul_left, tsum_geometric_of_lt_one ratioNonnegative small] using
    summable.tsum_le_tsum bound geometric

end EulerNonuniqueness.Paper.MovingMaterialPatch
