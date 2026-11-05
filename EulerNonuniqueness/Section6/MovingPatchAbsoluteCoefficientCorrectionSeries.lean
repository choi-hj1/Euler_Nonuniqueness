import EulerNonuniqueness.Section6.MovingPatchSourceCentroidCorrection

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.MovingMaterialPatch

set_option maxHeartbeats 400000

private theorem absolute_correction_bound (path : MovingMaterialPatch) (density : ℝ) (receiver : ℂ)
    (power : ℕ) (time : ℝ) {receiverRadius distance : ℝ}
    (receiverNonnegative : 0 ≤ receiverRadius) (positive : 0 < distance)
    (centered : path.center time = path.centroid time)
    (area : volume.real (path.domain time) = Real.pi * path.radius ^ 2)
    (separated : 2 * path.radius + distance ≤ ‖receiver - path.center time‖) :
    ‖path.sourceTaylorCentroidCorrection density receiver receiverRadius power time‖ ≤
      (2 * |density| * path.radius ^ 4) * (receiverRadius / distance) ^ power *
        ((power + 2 : ℝ) * (power + 3 : ℝ) * distance⁻¹ ^ 4) := by
  have radiusPositive := path.radius_positive
  have measurable := (path.domain_isOpen time).measurableSet
  have finite : volume (path.domain time) < ⊤ := (path.domain_isBounded time).measure_lt_top
  have bounded (source : ℂ) (member : source ∈ path.domain time) : ‖source - path.center time‖ ≤ 2 * path.radius :=
    (Metric.mem_ball.mp (path.domain_subset_ball time member)).le
  have identity := EulerNonuniqueness.Section6.centeredDomainInversePowerCorrection_eq_integral_remainder
    measurable finite (path.center time) receiver (power + 1) positive bounded separated
    (path.domain_centered_integral_zero_of_true_centroid time centered)
  have estimate := norm_integral_le_of_norm_le (μ := volume.restrict (path.domain time))
    (f := fun source : ℂ => EulerNonuniqueness.Section6.conjugateInversePowerTaylorRemainder
      (receiver - path.center time) (power + 1) (source - path.center time))
    (g := fun _ : ℂ => (power + 2 : ℝ) * (power + 3 : ℝ) * distance⁻¹ ^ (power + 4) * (2 * path.radius) ^ 2)
    (show Integrable (fun _ : ℂ =>
      (power + 2 : ℝ) * (power + 3 : ℝ) * distance⁻¹ ^ (power + 4) * (2 * path.radius) ^ 2)
      (volume.restrict (path.domain time)) from integrableOn_const.mpr (Or.inr finite)) (by
      filter_upwards [ae_restrict_mem measurable] with source member
      have actual := EulerNonuniqueness.Section6.conjugateInversePowerTaylorRemainder_norm_le
        (receiver - path.center time) (source - path.center time) (power + 1)
        (by positivity : 0 ≤ 2 * path.radius) positive separated (bounded source member)
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, Nat.reduceAdd] at actual
      apply actual.trans
      have scalar := mul_le_mul_of_nonneg_left (bounded source member)
        (show 0 ≤ (power + 2 : ℝ) * (power + 3 : ℝ) * distance⁻¹ ^ (power + 4) * (2 * path.radius) by positivity)
      convert scalar using 1 <;> ring)
  have correction : ‖EulerNonuniqueness.Section6.centeredDomainInversePowerCorrection
      (path.domain time) (path.center time) receiver (power + 1)‖ ≤
      (Real.pi * path.radius ^ 2) *
        ((power + 2 : ℝ) * (power + 3 : ℝ) * distance⁻¹ ^ (power + 4) * (2 * path.radius) ^ 2) := by
    rw [identity]
    have measureArea : (volume (path.domain time)).toReal = Real.pi * path.radius ^ 2 := area
    simpa only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul, measureArea, mul_comm] using estimate
  unfold sourceTaylorCentroidCorrection
  rw [norm_mul, norm_smul, Real.norm_eq_abs]
  have prefactorNorm :
      ‖(-1 : ℂ) ^ (power + 1) * Complex.I * (receiverRadius : ℂ) ^ power / ((2 * Real.pi : ℝ) : ℂ)‖ =
        receiverRadius ^ power / (2 * Real.pi) := by
    simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg receiverNonnegative,
      abs_of_pos (by positivity : 0 < 2 * Real.pi), abs_of_pos Real.pi_pos, one_mul]; norm_num
  rw [prefactorNorm]
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left correction (abs_nonneg density))
    (by positivity : 0 ≤ receiverRadius ^ power / (2 * Real.pi))).trans_eq
  simp only [div_pow, pow_add]
  field_simp
  ring

theorem sourceTaylorCentroidCorrection_summable_and_tsum_le (path : MovingMaterialPatch)
    (density : ℝ) (receiver : ℂ) (time : ℝ) {receiverRadius distance weight : ℝ}
    (receiverNonnegative : 0 ≤ receiverRadius) (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (centered : path.center time = path.centroid time)
    (area : volume.real (path.domain time) = Real.pi * path.radius ^ 2)
    (separated : 2 * path.radius + distance ≤ ‖receiver - path.center time‖)
    (small : 4 * weight * receiverRadius / distance < 1) :
    Summable (fun power : ℕ => weight ^ (power + 1) *
      ‖path.sourceTaylorCentroidCorrection density receiver receiverRadius power time‖) ∧
    (∑' power : ℕ, weight ^ (power + 1) *
      ‖path.sourceTaylorCentroidCorrection density receiver receiverRadius power time‖) ≤
      (64 * weight * |density| * path.radius ^ 4 * distance⁻¹ ^ 4) *
        (1 - 4 * weight * receiverRadius / distance)⁻¹ := by
  have ratioNonnegative : 0 ≤ 4 * weight * receiverRadius / distance := by positivity
  have geometric := (summable_geometric_of_lt_one ratioNonnegative small).mul_left
    (64 * weight * |density| * path.radius ^ 4 * distance⁻¹ ^ 4)
  have bound (power : ℕ) : weight ^ (power + 1) *
      ‖path.sourceTaylorCentroidCorrection density receiver receiverRadius power time‖ ≤
      (64 * weight * |density| * path.radius ^ 4 * distance⁻¹ ^ 4) *
        (4 * weight * receiverRadius / distance) ^ power := by
    have firstDegree : (power + 2 : ℝ) ≤ 4 * (2 : ℝ) ^ power := by
      have actual : (power + 2 : ℝ) ≤ (2 : ℝ) ^ (power + 2) := by
        exact_mod_cast (Nat.lt_two_pow_self (n := power + 2)).le
      simpa only [pow_add, show (2 : ℝ) ^ 2 = 4 by norm_num, mul_comm] using actual
    have secondDegree : (power + 3 : ℝ) ≤ 8 * (2 : ℝ) ^ power := by
      have actual : (power + 3 : ℝ) ≤ (2 : ℝ) ^ (power + 3) := by
        exact_mod_cast (Nat.lt_two_pow_self (n := power + 3)).le
      simpa only [pow_add, show (2 : ℝ) ^ 3 = 8 by norm_num, mul_comm] using actual
    have quadraticDegree : (power + 2 : ℝ) * (power + 3 : ℝ) ≤ 32 * (4 : ℝ) ^ power := by
      apply (mul_le_mul firstDegree secondDegree (by positivity) (by positivity)).trans_eq
      rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
      ring
    have actual := mul_le_mul_of_nonneg_left
      (absolute_correction_bound path density receiver power time receiverNonnegative positive centered area separated)
      (pow_nonneg weightNonnegative (power + 1))
    apply actual.trans
    calc
      _ ≤ weight ^ (power + 1) * ((2 * |density| * path.radius ^ 4) * (receiverRadius / distance) ^ power *
          ((32 * (4 : ℝ) ^ power) * distance⁻¹ ^ 4)) := by gcongr
      _ = _ := by simp only [pow_succ, mul_pow, div_pow]; ring
  have summable := Summable.of_nonneg_of_le (fun power => by positivity) bound geometric
  refine ⟨summable, ?_⟩
  simpa only [tsum_mul_left, tsum_geometric_of_lt_one ratioNonnegative small] using
    summable.tsum_le_tsum bound geometric

end EulerNonuniqueness.Paper.MovingMaterialPatch
