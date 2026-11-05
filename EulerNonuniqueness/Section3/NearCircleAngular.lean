import EulerNonuniqueness.Section3.CircleBanach
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

def nearCircleRatio (data : PeriodicC1HolderHalf) (label : ℝ) : ℂ :=
  data.val.1 label / standardCircle label

def nearCircleAngularLift (data : PeriodicC1HolderHalf) (label : ℝ) : ℝ :=
  label + (Complex.log (nearCircleRatio data label)).im

theorem nearCircleRatio_close_one (data : PeriodicC1HolderHalf) (label : ℝ) :
    ‖nearCircleRatio data label - 1‖ ≤ ‖data - standardCircleBanach‖ := by
  have nonzero : standardCircle label ≠ 0 := norm_ne_zero_iff.mp (by rw [standardCircle_norm]; norm_num)
  rw [nearCircleRatio, div_sub_one nonzero, norm_div, standardCircle_norm, div_one]
  exact PeriodicC1HolderHalf.value_bound (data - standardCircleBanach) label

theorem nearCircleRatio_mem_slitPlane (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1) (label : ℝ) :
    nearCircleRatio data label ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  have estimate := (Complex.abs_re_le_norm (nearCircleRatio data label - 1)).trans
    (nearCircleRatio_close_one data label)
  rw [Complex.sub_re, Complex.one_re] at estimate
  have lower := (abs_le.mp estimate).1
  linarith

theorem nearCircleRatio_periodic (data : PeriodicC1HolderHalf) :
    Function.Periodic (nearCircleRatio data) (2 * Real.pi) := by
  intro label
  unfold nearCircleRatio
  rw [PeriodicC1HolderHalf.periodic data label, standardCircle_periodic label]

theorem nearCircleAngularLift_add_period (data : PeriodicC1HolderHalf) (label : ℝ) :
    nearCircleAngularLift data (label + 2 * Real.pi) = nearCircleAngularLift data label + 2 * Real.pi := by
  unfold nearCircleAngularLift
  rw [nearCircleRatio_periodic data label]
  ring

theorem nearCircleAngularLift_deviation_bound (data : PeriodicC1HolderHalf) (label : ℝ) :
    |nearCircleAngularLift data label - label| ≤ Real.pi := by
  unfold nearCircleAngularLift
  rw [add_sub_cancel_left]
  exact abs_le.mpr ⟨(Complex.neg_pi_lt_log_im _).le, Complex.log_im_le_pi _⟩

theorem nearCircle_value_lower_bound (data : PeriodicC1HolderHalf) (label : ℝ) :
    1 - ‖data - standardCircleBanach‖ ≤ ‖data.val.1 label‖ := by
  have estimate := norm_sub_norm_le (standardCircle label) (data.val.1 label)
  rw [standardCircle_norm, norm_sub_rev] at estimate
  have difference_bound := PeriodicC1HolderHalf.value_bound (data - standardCircleBanach) label
  change ‖data.val.1 label - standardCircle label‖ ≤ ‖data - standardCircleBanach‖ at difference_bound
  linarith

set_option maxHeartbeats 1000000 in
theorem nearCircleAngularLift_hasDerivAt (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1) (label : ℝ) :
    HasDerivAt (nearCircleAngularLift data) ((data.val.2.val.1 label / data.val.1 label).im) label := by
  have circle_ne : standardCircle label ≠ 0 := norm_ne_zero_iff.mp (by rw [standardCircle_norm]; norm_num)
  have value_ne : data.val.1 label ≠ 0 := norm_pos_iff.mp (by
    have lower := nearCircle_value_lower_bound data label
    linarith)
  have ratio_derivative := (PeriodicC1HolderHalf.hasDerivAt data label).div (standardCircle_derivative label) circle_ne
  have log_derivative := (Complex.hasDerivAt_log (nearCircleRatio_mem_slitPlane data small label)).scomp label ratio_derivative
  have actual_log_derivative : HasDerivAt (fun parameter => Complex.log (nearCircleRatio data parameter))
      (data.val.2.val.1 label / data.val.1 label - Complex.I) label := by
    convert log_derivative using 1
    simp only [nearCircleRatio, standardCircleTangent, smul_eq_mul]
    field_simp
    <;> ring
  have imaginary_derivative := (Complex.imCLM.hasFDerivAt).comp_hasDerivAt label actual_log_derivative
  have actual := (hasDerivAt_id label).add imaginary_derivative
  convert actual using 1
  simp only [Complex.imCLM_apply, Complex.sub_im, Complex.I_im]
  ring

theorem nearCircleAngularLift_derivative_pos (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) (label : ℝ) :
    0 < (data.val.2.val.1 label / data.val.1 label).im := by
  have lower := nearCircle_value_lower_bound data label
  have value_pos : 0 < ‖data.val.1 label‖ := by linarith
  have value_ne := norm_pos_iff.mp value_pos
  have value_difference := PeriodicC1HolderHalf.value_bound (data - standardCircleBanach) label
  change ‖data.val.1 label - standardCircle label‖ ≤ ‖data - standardCircleBanach‖ at value_difference
  have numerator_bound : ‖data.val.2.val.1 label - Complex.I * data.val.1 label‖ ≤
      2 * ‖data - standardCircleBanach‖ := by
    have identity : data.val.2.val.1 label - Complex.I * data.val.1 label =
        (data.val.2.val.1 label - standardCircleTangent label) +
          Complex.I * (standardCircle label - data.val.1 label) := by unfold standardCircleTangent; ring
    rw [identity]
    apply (norm_add_le _ _).trans
    rw [norm_mul, Complex.norm_I, one_mul, norm_sub_rev (standardCircle label) (data.val.1 label)]
    have tangent_difference := PeriodicC1HolderHalf.derivative_close_circle data label
    linarith
  have error_identity : data.val.2.val.1 label / data.val.1 label - Complex.I =
      (data.val.2.val.1 label - Complex.I * data.val.1 label) / data.val.1 label := by
    field_simp
    ring
  have error_small : ‖data.val.2.val.1 label / data.val.1 label - Complex.I‖ < 1 := by
    rw [error_identity, norm_div]
    apply (div_lt_one value_pos).mpr
    linarith
  have imaginary_small := (Complex.abs_im_le_norm
    (data.val.2.val.1 label / data.val.1 label - Complex.I)).trans_lt error_small
  rw [Complex.sub_im, Complex.I_im] at imaginary_small
  have bound := (abs_lt.mp imaginary_small).1
  linarith

theorem nearCircleAngularLift_strictMono (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) : StrictMono (nearCircleAngularLift data) :=
  strictMono_of_hasDerivAt_pos
    (nearCircleAngularLift_hasDerivAt data (small.trans (by norm_num)))
    (nearCircleAngularLift_derivative_pos data small)

theorem nearCircleAngularLift_continuous (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1) : Continuous (nearCircleAngularLift data) :=
  continuous_iff_continuousAt.mpr (fun label => (nearCircleAngularLift_hasDerivAt data small label).continuousAt)

theorem nearCircleAngularLift_surjective (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1) : Function.Surjective (nearCircleAngularLift data) := by
  intro angle
  apply Set.mem_range.mp
  apply mem_range_of_exists_le_of_exists_ge (nearCircleAngularLift_continuous data small)
  · refine ⟨angle - Real.pi - 1, ?_⟩
    have bound := (abs_le.mp (nearCircleAngularLift_deviation_bound data (angle - Real.pi - 1))).2
    linarith
  · refine ⟨angle + Real.pi + 1, ?_⟩
    have bound := (abs_le.mp (nearCircleAngularLift_deviation_bound data (angle + Real.pi + 1))).1
    linarith

end

end EulerNonuniqueness.Paper
