import EulerNonuniqueness.Section6.MovingPatchSourceCentroidCorrection
import EulerNonuniqueness.Section6.PatchCrossInteraction

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.MovingMaterialPatch

set_option maxHeartbeats 1000000

def sourceVelocityCentroidCorrection (path : MovingMaterialPatch) (density : ℝ)
    (receiver : ℂ) (time : ℝ) : ℂ :=
  (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) *
    (density • Section6.centeredDomainInversePowerCorrection
      (path.domain time) (path.center time) receiver 0)

theorem sourceVelocity_eq_centroid_and_correction (path : MovingMaterialPatch)
    (density : ℝ) (receiver : ℂ) (time : ℝ) :
    biotSavart ((path.domain time).indicator (fun _ => density)) receiver =
      (density * volume.real (path.domain time)) •
          biotSavartKernel (receiver - path.center time) +
        path.sourceVelocityCentroidCorrection density receiver time := by
  rw [Section6.biotSavart_indicator_density_integral (path.domain_isOpen time).measurableSet]
  simp_rw [biotSavartKernel_eq_conj_inv]
  rw [integral_const_mul]
  simp only [sourceVelocityCentroidCorrection, Section6.centeredDomainInversePowerCorrection,
    Nat.zero_add, pow_one, Complex.real_smul, Complex.ofReal_mul, starRingEnd_apply]
  ring

theorem sourceVelocityCentroidCorrection_receiver_difference_norm_le (path : MovingMaterialPatch)
    (density : ℝ) (anchor first second : ℂ) (time : ℝ)
    {travel distance : ℝ} (travelNonnegative : 0 ≤ travel) (positive : 0 < distance)
    (centered : path.center time = path.centroid time)
    (area : volume.real (path.domain time) = Real.pi * path.radius ^ 2)
    (separated : 2 * path.radius + travel + distance ≤ ‖anchor - path.center time‖)
    (firstBound : ‖first - anchor‖ ≤ travel) (secondBound : ‖second - anchor‖ ≤ travel) :
    ‖path.sourceVelocityCentroidCorrection density first time -
      path.sourceVelocityCentroidCorrection density second time‖ ≤
        12 * |density| * path.radius ^ 4 * distance⁻¹ ^ 4 * ‖first - second‖ := by
  have bounded (source : ℂ) (member : source ∈ path.domain time) :
      ‖source - path.center time‖ ≤ 2 * path.radius :=
    (Metric.mem_ball.mp (path.domain_subset_ball time member)).le
  have radiusPositive := path.radius_positive
  have actual := Section6.centeredDomainInversePowerCorrection_receiver_difference_norm_le
    (path.domain_isOpen time).measurableSet (path.domain_isBounded time).measure_lt_top
    (path.center time) anchor first second 0 (by positivity) travelNonnegative positive
    bounded separated firstBound secondBound
    (path.domain_centered_integral_zero_of_true_centroid time centered)
  rw [area] at actual
  norm_num only [Nat.cast_zero, zero_add, Nat.reduceAdd] at actual
  unfold sourceVelocityCentroidCorrection
  rw [← mul_sub, ← smul_sub, norm_mul, norm_smul, Real.norm_eq_abs]
  have prefactorNorm : ‖Complex.I / ((2 * Real.pi : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
    simp only [norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  rw [prefactorNorm]
  apply (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left actual (abs_nonneg density))
    (by positivity : 0 ≤ 1 / (2 * Real.pi))).trans_eq
  field_simp
  <;> ring

end EulerNonuniqueness.Paper.MovingMaterialPatch
