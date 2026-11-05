import EulerNonuniqueness.General.FlowLinearizationEstimate
import EulerNonuniqueness.General.CompactTaylorRemainder
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section

open Set Filter Metric Asymptotics
open scoped NNReal Topology

namespace EulerNonuniqueness

theorem hasFDerivAt_flow_of_variational {Parameter Space : Type*}
    [PseudoMetricSpace Parameter] [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    {field : Parameter → Space → Space}
    {fieldDerivative : Parameter → Space → Space →L[ℝ] Space}
    (derivativeContinuous : Continuous (fun point : Parameter × Space => fieldDerivative point.1 point.2))
    (fieldDifferentiable : ∀ parameter position,
      HasFDerivAt (field parameter) (fieldDerivative parameter position) position)
    {bound : ℝ≥0} (lipschitz : ∀ parameter, LipschitzWith bound (field parameter))
    {horizon : ℝ} {parameter : ℝ → Parameter}
    (parameterContinuous : ContinuousOn parameter (Icc 0 horizon))
    {flow : ℝ → Space → Space} (initial : ∀ position, flow 0 position = position)
    (continuous : ∀ position, ContinuousOn (fun time => flow time position) (Icc 0 horizon))
    (equation : ∀ position time, time ∈ Ico 0 horizon →
      HasDerivWithinAt (fun next => flow next position)
        (field (parameter time) (flow time position)) (Ici time) time)
    {jacobian : ℝ → Space →L[ℝ] Space} (position : Space)
    (jacobianInitial : jacobian 0 = ContinuousLinearMap.id ℝ Space)
    (jacobianContinuous : ContinuousOn jacobian (Icc 0 horizon))
    (jacobianEquation : ∀ direction time, time ∈ Ico 0 horizon →
      HasDerivWithinAt (fun next => jacobian next direction)
        (fieldDerivative (parameter time) (flow time position) (jacobian time direction)) (Ici time) time)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    HasFDerivAt (flow time) (jacobian time) position := by
  obtain ⟨operatorConstant, operatorBound⟩ := isCompact_Icc.exists_bound_of_continuousOn jacobianContinuous
  let operatorSize := |operatorConstant| + 1
  have operatorPositive : 0 < operatorSize := by dsimp [operatorSize]; positivity
  have operatorEstimate (next : ℝ) (nextInside : next ∈ Icc 0 horizon) : ‖jacobian next‖ ≤ operatorSize :=
    (operatorBound next nextInside).trans ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one))
  have graphCompact : IsCompact ((fun next => (parameter next, flow next position)) '' Icc 0 horizon) :=
    isCompact_Icc.image_of_continuousOn (parameterContinuous.prodMk (continuous position))
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro target targetPositive
  let factor := |gronwallBound 0 bound 1 time| + 1
  have factorPositive : 0 < factor := by dsimp [factor]; positivity
  let error := target / factor
  have errorPositive : 0 < error := div_pos targetPositive factorPositive
  obtain ⟨radius, radiusPositive, taylor⟩ := uniform_taylor_remainder_near_compact
    derivativeContinuous fieldDifferentiable graphCompact (div_pos errorPositive operatorPositive)
  filter_upwards [Metric.ball_mem_nhds (0 : Space) (div_pos radiusPositive operatorPositive)] with increment small
  have smallNorm : ‖increment‖ < radius / operatorSize := by simpa only [mem_ball, dist_zero_right] using small
  have remainder (next : ℝ) (nextInside : next ∈ Ico 0 horizon) :
      dist (field (parameter next) (flow next position) +
        fieldDerivative (parameter next) (flow next position) (jacobian next increment))
        (field (parameter next) (flow next position + jacobian next increment)) ≤ error * ‖increment‖ := by
    have nextClosed : next ∈ Icc 0 horizon := ⟨nextInside.1, nextInside.2.le⟩
    have incrementBound : ‖jacobian next increment‖ ≤ operatorSize * ‖increment‖ :=
      ((jacobian next).le_opNorm increment).trans
        (mul_le_mul_of_nonneg_right (operatorEstimate next nextClosed) (norm_nonneg _))
    have incrementSmall : ‖jacobian next increment‖ < radius := incrementBound.trans_lt (by
      simpa only [mul_comm] using (lt_div_iff₀ operatorPositive).mp smallNorm)
    have estimate := taylor (parameter next) (flow next position)
      (mem_image_of_mem _ nextClosed) (jacobian next increment) incrementSmall
    calc
      _ = ‖field (parameter next) (flow next position + jacobian next increment) -
          field (parameter next) (flow next position) -
          fieldDerivative (parameter next) (flow next position) (jacobian next increment)‖ := by
        rw [dist_eq_norm, ← norm_neg]
        congr 1
        abel
      _ ≤ (error / operatorSize) * ‖jacobian next increment‖ := estimate
      _ ≤ (error / operatorSize) * (operatorSize * ‖increment‖) :=
        mul_le_mul_of_nonneg_left incrementBound (div_nonneg errorPositive.le operatorPositive.le)
      _ = error * ‖increment‖ := by field_simp; ring
  have estimate := dist_flow_linearization_le (fun next => lipschitz (parameter next)) initial continuous equation
    jacobianInitial jacobianContinuous jacobianEquation position increment remainder inside
  have homogeneous : gronwallBound 0 bound (error * ‖increment‖) time =
      error * ‖increment‖ * gronwallBound 0 bound 1 time := by
    unfold gronwallBound
    split_ifs <;> ring
  have factorBound : error * gronwallBound 0 bound 1 time ≤ target := by
    calc
      _ ≤ error * factor := mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one)) errorPositive.le
      _ = target := div_mul_cancel₀ _ factorPositive.ne'
  rw [homogeneous] at estimate
  have finalBound : dist (flow time (position + increment))
      (flow time position + jacobian time increment) ≤ target * ‖increment‖ := estimate.trans (by
    nlinarith [mul_le_mul_of_nonneg_right factorBound (norm_nonneg increment)])
  simpa only [dist_eq_norm, sub_add_eq_sub_sub] using finalBound

end EulerNonuniqueness
