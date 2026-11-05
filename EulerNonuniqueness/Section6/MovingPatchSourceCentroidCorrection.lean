import EulerNonuniqueness.Section6.MovingPatchSourceCoefficient
import EulerNonuniqueness.Section6.CenteredDomainInversePowerCorrection

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.MovingMaterialPatch

set_option maxHeartbeats 1000000

def sourceTaylorCentroidCorrection (path : MovingMaterialPatch) (density : ℝ) (receiver : ℂ)
    (receiverRadius : ℝ) (power : ℕ) (time : ℝ) : ℂ :=
  ((-1 : ℂ) ^ (power + 1) * Complex.I * (receiverRadius : ℂ) ^ power / ((2 * Real.pi : ℝ) : ℂ)) *
    (density • Section6.centeredDomainInversePowerCorrection
      (path.domain time) (path.center time) receiver (power + 1))

theorem sourceTaylorCoefficient_eq_centroid_and_correction (path : MovingMaterialPatch)
    (density : ℝ) (receiver : ℂ) (receiverRadius : ℝ) (power : ℕ) (time : ℝ) :
    path.sourceTaylorCoefficient density receiver receiverRadius power time =
      ((-1 : ℂ) ^ (power + 1) * Complex.I * (receiverRadius : ℂ) ^ power / ((2 * Real.pi : ℝ) : ℂ)) *
        ((density * volume.real (path.domain time)) • (star (receiver - path.center time))⁻¹ ^ (power + 2)) +
      path.sourceTaylorCentroidCorrection density receiver receiverRadius power time := by
  simp only [sourceTaylorCoefficient, sourceTaylorCentroidCorrection, Section6.centeredDomainInversePowerCorrection,
    Complex.real_smul, Complex.ofReal_mul, Nat.add_assoc, Nat.reduceAdd]
  ring

theorem domain_centered_integral_zero_of_true_centroid (path : MovingMaterialPatch) (time : ℝ)
    (centered : path.center time = path.centroid time) :
    (∫ position in path.domain time, position - path.center time) = 0 := by
  have identityIntegrable := path.integral_continuous_function time (continuous_id : Continuous (fun position : ℂ => position))
  have constantIntegrable := path.integral_continuous_function time
    (continuous_const : Continuous (fun _ : ℂ => path.center time))
  have momentIdentity : (∫ position in path.domain time, position) = volume.real (path.domain time) • path.center time := by
    have scaled := congrArg (fun value : ℂ => volume.real (path.domain time) • value) centered
    dsimp only at scaled
    rw [centroid, smul_smul, mul_inv_cancel₀ (path.domain_area_positive time).ne', one_smul] at scaled
    exact scaled.symm
  have split := integral_sub identityIntegrable constantIntegrable
  change (∫ position in path.domain time, position - path.center time) = _ at split
  rw [split, integral_const]
  simp only [id_eq, momentIdentity, Measure.real, Measure.restrict_apply_univ, sub_self]

theorem sourceTaylorCentroidCorrection_receiver_difference_norm_le (path : MovingMaterialPatch)
    (density : ℝ) (anchor first second : ℂ) (power : ℕ) (time : ℝ)
    {receiverRadius travel distance : ℝ} (receiverNonnegative : 0 ≤ receiverRadius)
    (travelNonnegative : 0 ≤ travel) (positive : 0 < distance)
    (centered : path.center time = path.centroid time)
    (area : volume.real (path.domain time) = Real.pi * path.radius ^ 2)
    (separated : 2 * path.radius + travel + distance ≤ ‖anchor - path.center time‖)
    (firstBound : ‖first - anchor‖ ≤ travel) (secondBound : ‖second - anchor‖ ≤ travel) :
    ‖path.sourceTaylorCentroidCorrection density first receiverRadius power time -
      path.sourceTaylorCentroidCorrection density second receiverRadius power time‖ ≤
      (2 * |density| * path.radius ^ 4) * (receiverRadius / distance) ^ power *
        ((power + 2 : ℝ) * (power + 3 : ℝ) * (power + 4 : ℝ) * distance⁻¹ ^ 5) * ‖first - second‖ := by
  have radiusPositive := path.radius_positive
  have bounded (source : ℂ) (member : source ∈ path.domain time) : ‖source - path.center time‖ ≤ 2 * path.radius := by
    exact (Metric.mem_ball.mp (path.domain_subset_ball time member)).le
  have actual := Section6.centeredDomainInversePowerCorrection_receiver_difference_norm_le
    (path.domain_isOpen time).measurableSet (path.domain_isBounded time).measure_lt_top
    (path.center time) anchor first second (power + 1) (by positivity) travelNonnegative positive
    bounded separated firstBound secondBound (path.domain_centered_integral_zero_of_true_centroid time centered)
  rw [area] at actual
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, Nat.reduceAdd] at actual
  unfold sourceTaylorCentroidCorrection
  rw [← mul_sub, ← smul_sub, norm_mul, norm_smul, Real.norm_eq_abs]
  have prefactorNorm :
      ‖(-1 : ℂ) ^ (power + 1) * Complex.I * (receiverRadius : ℂ) ^ power / ((2 * Real.pi : ℝ) : ℂ)‖ =
        receiverRadius ^ power / (2 * Real.pi) := by
    simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg receiverNonnegative,
      abs_of_pos (by positivity : 0 < 2 * Real.pi), abs_of_pos Real.pi_pos, one_mul] <;> norm_num
  rw [prefactorNorm]
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left actual (abs_nonneg density))
    (by positivity : 0 ≤ receiverRadius ^ power / (2 * Real.pi))).trans_eq
  simp only [div_pow, pow_add]
  field_simp
  <;> ring

end EulerNonuniqueness.Paper.MovingMaterialPatch
