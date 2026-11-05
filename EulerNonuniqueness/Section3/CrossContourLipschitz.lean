import EulerNonuniqueness.Section3.CrossContourNorms

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

local instance crossLipschitzHolderNormedSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance crossLipschitzC1NormedSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance crossLipschitzBoundedSMul : IsBoundedSMul ℝ PeriodicC1HolderHalf :=
  NormedSpace.isBoundedSMul (𝕜 := ℝ) (E := PeriodicC1HolderHalf)

def crossContourPhaseBound (bound lower : ℝ) : ℝ :=
  16 * bound * c1InverseUniformBound (2 * bound) lower

def crossContourPhaseLipschitzBound (bound lower : ℝ) : ℝ :=
  8 * c1InverseUniformBound (2 * bound) lower +
    1024 * bound * (c1InverseUniformBound (2 * bound) lower)^2

def crossContourIntegrandLipschitzBound (bound lower : ℝ) : ℝ :=
  8 * bound * crossContourPhaseLipschitzBound bound lower + 8 * crossContourPhaseBound bound lower

set_option maxHeartbeats 1000000 in
theorem crossContourPhaseIntegrand_parameter_norm_bound
    (firstTarget firstSource secondTarget secondSource : PeriodicC1HolderHalf)
    {lower bound : ℝ} (lower_pos : 0 < lower)
    (first_separated : ∀ sourceLabel targetLabel,
      lower ≤ ‖firstTarget.val.1 targetLabel - firstSource.val.1 sourceLabel‖)
    (second_separated : ∀ sourceLabel targetLabel,
      lower ≤ ‖secondTarget.val.1 targetLabel - secondSource.val.1 sourceLabel‖)
    (first_target_bound : ‖firstTarget‖ ≤ bound) (first_source_bound : ‖firstSource‖ ≤ bound)
    (second_target_bound : ‖secondTarget‖ ≤ bound) (second_source_bound : ‖secondSource‖ ≤ bound)
    (label : ℝ) :
    ‖crossContourPhaseIntegrand firstTarget firstSource lower_pos first_separated label -
      crossContourPhaseIntegrand secondTarget secondSource lower_pos second_separated label‖ ≤
      crossContourIntegrandLipschitzBound bound lower *
        (‖firstTarget - secondTarget‖ + ‖firstSource - secondSource‖) := by
  let first_difference := crossContourDifference firstTarget (firstSource.val.1 label)
  let second_difference := crossContourDifference secondTarget (secondSource.val.1 label)
  let first_phase := c1Phase first_difference lower_pos (first_separated label)
  let second_phase := c1Phase second_difference lower_pos (second_separated label)
  let first_tangent := c1Constant (star (firstSource.val.2.val.1 label))
  let second_tangent := c1Constant (star (secondSource.val.2.val.1 label))
  have bound_nonneg := (norm_nonneg firstTarget).trans first_target_bound
  have first_difference_bound : ‖first_difference‖ ≤ 2 * bound :=
    (crossContourDifference_norm_bound firstTarget firstSource label).trans
      (by linarith)
  have second_difference_bound : ‖second_difference‖ ≤ 2 * bound :=
    (crossContourDifference_norm_bound secondTarget secondSource label).trans
      (by linarith)
  have phase_lip_nonneg : 0 ≤ crossContourPhaseLipschitzBound bound lower := by
    have inverse_nonneg : 0 ≤ c1InverseUniformBound (2 * bound) lower :=
      (by positivity : 0 ≤ 1 / lower).trans (le_max_left _ _)
    unfold crossContourPhaseLipschitzBound
    positivity
  have phase_difference : ‖first_phase - second_phase‖ ≤ crossContourPhaseLipschitzBound bound lower *
      (‖firstTarget - secondTarget‖ + ‖firstSource - secondSource‖) := by
    have estimate := c1Phase_difference_norm_bound first_difference second_difference lower_pos
      (first_separated label) (second_separated label) first_difference_bound second_difference_bound
    have difference_bound := crossContourDifference_parameter_norm_bound firstTarget firstSource secondTarget secondSource label
    have constant_eq : 8 * c1InverseUniformBound (2 * bound) lower +
        512 * (2 * bound) * c1InverseUniformBound (2 * bound) lower ^ 2 =
        crossContourPhaseLipschitzBound bound lower := by unfold crossContourPhaseLipschitzBound; ring
    rw [constant_eq] at estimate
    exact estimate.trans (mul_le_mul_of_nonneg_left difference_bound phase_lip_nonneg)
  have phase_bound : ‖second_phase‖ ≤ crossContourPhaseBound bound lower := by
    have estimate := c1Phase_uniform_norm_bound second_difference lower_pos
      (second_separated label) second_difference_bound
    exact estimate.trans_eq (by unfold crossContourPhaseBound; ring)
  have first_tangent_bound : ‖first_tangent‖ ≤ bound := by
    apply (c1Constant_norm_bound _).trans
    rw [norm_star]
    exact (PeriodicC1HolderHalf.speed_bound firstSource label).trans first_source_bound
  have tangent_difference := crossContourTangent_parameter_norm_bound firstSource secondSource label
  have phase_bound_nonneg : 0 ≤ crossContourPhaseBound bound lower := (norm_nonneg second_phase).trans phase_bound
  change ‖c1Product first_phase first_tangent - c1Product second_phase second_tangent‖ ≤ _
  apply (c1Product_difference_norm_bound first_phase first_tangent second_phase second_tangent).trans
  have left : 8 * ‖first_phase - second_phase‖ * ‖first_tangent‖ ≤
      8 * (crossContourPhaseLipschitzBound bound lower *
        (‖firstTarget - secondTarget‖ + ‖firstSource - secondSource‖)) * bound :=
    mul_le_mul (mul_le_mul_of_nonneg_left phase_difference (by norm_num)) first_tangent_bound
      (norm_nonneg _) (by positivity)
  have right : 8 * ‖second_phase‖ * ‖first_tangent - second_tangent‖ ≤
      8 * crossContourPhaseBound bound lower * ‖firstSource - secondSource‖ :=
    mul_le_mul (mul_le_mul_of_nonneg_left phase_bound (by norm_num)) tangent_difference
      (norm_nonneg _) (by positivity)
  have source_le : ‖firstSource - secondSource‖ ≤ ‖firstTarget - secondTarget‖ + ‖firstSource - secondSource‖ :=
    le_add_of_nonneg_left (norm_nonneg _)
  have right_larger := mul_le_mul_of_nonneg_left source_le (show 0 ≤ 8 * crossContourPhaseBound bound lower by positivity)
  unfold crossContourIntegrandLipschitzBound
  nlinarith

set_option maxHeartbeats 1000000 in
theorem crossContourVelocityBanach_parameter_norm_bound
    (firstTarget firstSource secondTarget secondSource : PeriodicC1HolderHalf)
    {lower bound : ℝ} (lower_pos : 0 < lower)
    (first_separated : ∀ sourceLabel targetLabel,
      lower ≤ ‖firstTarget.val.1 targetLabel - firstSource.val.1 sourceLabel‖)
    (second_separated : ∀ sourceLabel targetLabel,
      lower ≤ ‖secondTarget.val.1 targetLabel - secondSource.val.1 sourceLabel‖)
    (first_target_bound : ‖firstTarget‖ ≤ bound) (first_source_bound : ‖firstSource‖ ≤ bound)
    (second_target_bound : ‖secondTarget‖ ≤ bound) (second_source_bound : ‖secondSource‖ ≤ bound) :
    ‖crossContourVelocityBanach firstTarget firstSource lower_pos first_separated -
      crossContourVelocityBanach secondTarget secondSource lower_pos second_separated‖ ≤
      (crossContourIntegrandLipschitzBound bound lower / 2) *
        (‖firstTarget - secondTarget‖ + ‖firstSource - secondSource‖) := by
  have first_integrable : IntervalIntegrable
      (crossContourPhaseIntegrand firstTarget firstSource lower_pos first_separated)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (crossContourPhaseIntegrand_continuous firstTarget firstSource lower_pos first_separated).intervalIntegrable _ _
  have second_integrable : IntervalIntegrable
      (crossContourPhaseIntegrand secondTarget secondSource lower_pos second_separated)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (crossContourPhaseIntegrand_continuous secondTarget secondSource lower_pos second_separated).intervalIntegrable _ _
  have integral_bound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -Real.pi) (b := Real.pi)
    (fun label _ => crossContourPhaseIntegrand_parameter_norm_bound firstTarget firstSource secondTarget secondSource lower_pos
      first_separated second_separated first_target_bound first_source_bound second_target_bound second_source_bound label)
  rw [crossContourVelocityBanach, crossContourVelocityBanach,
    ← smul_sub (1 / (4 * Real.pi) : ℝ)
      (∫ label in (-Real.pi)..Real.pi, crossContourPhaseIntegrand firstTarget firstSource lower_pos first_separated label)
      (∫ label in (-Real.pi)..Real.pi, crossContourPhaseIntegrand secondTarget secondSource lower_pos second_separated label),
    ← intervalIntegral.integral_sub first_integrable second_integrable, norm_smul]
  rw [Real.norm_eq_abs, abs_of_pos (show 0 < 1 / (4 * Real.pi) by positivity)]
  apply (mul_le_mul_of_nonneg_left integral_bound (by positivity)).trans_eq
  rw [show Real.pi - -Real.pi = 2 * Real.pi by ring, abs_of_pos (show 0 < 2 * Real.pi by positivity)]
  field_simp
  <;> ring

end

end EulerNonuniqueness.Paper
