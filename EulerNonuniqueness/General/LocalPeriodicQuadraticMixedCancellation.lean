import EulerNonuniqueness.General.LocalPeriodicExponentialVariation
import EulerNonuniqueness.General.QuadraticResonanceEvaluation
import EulerNonuniqueness.General.LinearGroupFixedVector

namespace EulerNonuniqueness.General

noncomputable section

open Filter Set MeasureTheory
open scoped Topology

set_option maxHeartbeats 1000000

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem localPeriodicExponentialVariation_mixed_resonance_zero
    (operator : ℝ → Space →L[ℝ] Space) (bilinear : BilinearEnd Space) (neutral : Space)
    {radius period : ℝ} (radiusPositive : 0 < radius) (periodPositive : 0 < period)
    (continuousOperator : ContinuousOn operator (Icc (-radius) radius))
    (operatorDerivative : HasDerivAt operator ((2 : ℝ) • bilinear neutral) 0)
    (periodic : ∀ᶠ parameter in 𝓝 (0 : ℝ),
      NormedSpace.exp ℝ (period • operator parameter) = ContinuousLinearMap.id ℝ Space)
    (kernel : operator 0 neutral = 0) (direction : Space) :
    quadraticResonance (linearExponentialGroup (operator 0)) period bilinear neutral direction = 0 := by
  let group := linearExponentialGroup (operator 0)
  have groupContinuous : Continuous group := continuous_iff_continuousAt.mpr (fun time =>
    (linearExponentialGroup_hasDerivAt_right (operator 0) time).continuousAt)
  have continuousConjugate : Continuous (fun time => quadraticConjugate group time bilinear) :=
    continuous_iff_continuousAt.mpr (fun time => HasDerivAt.continuousAt (F := BilinearEnd Space)
      (quadraticConjugate_hasDerivAt group (operator 0) (linearExponentialGroup_zero _)
        (linearExponentialGroup_add _) (linearExponentialGroup_hasDerivAt_right _) bilinear time))
  have fixed (time : ℝ) : group time neutral = neutral :=
    linearExponentialGroup_fixed_of_generator_zero (operator 0) kernel time
  have actual := localPeriodicExponentialVariation_operator_average_zero operator
    ((2 : ℝ) • bilinear neutral) radiusPositive periodPositive continuousOperator operatorDerivative periodic
  change (∫ time in (0 : ℝ)..period,
    (group (-time)).comp (((2 : ℝ) • bilinear neutral).comp (group time))) = 0 at actual
  have integrable : IntervalIntegrable
      (fun time => (group (-time)).comp (((2 : ℝ) • bilinear neutral).comp (group time))) volume 0 period :=
    ((groupContinuous.comp continuous_neg).clm_comp
      (continuous_const.clm_comp groupContinuous)).intervalIntegrable _ _
  have commutation :
      (∫ time in (0 : ℝ)..period, group (-time) (((2 : ℝ) • bilinear neutral) (group time direction))) =
      (∫ time in (0 : ℝ)..period,
        (group (-time)).comp (((2 : ℝ) • bilinear neutral).comp (group time))) direction :=
    (ContinuousLinearMap.apply ℝ Space direction).intervalIntegral_comp_comm integrable
  have evaluated := congrArg (fun linear : Space →L[ℝ] Space => linear direction) actual
  change (∫ time in (0 : ℝ)..period,
    (group (-time)).comp (((2 : ℝ) • bilinear neutral).comp (group time))) direction = 0 at evaluated
  rw [← commutation] at evaluated
  simp only [ContinuousLinearMap.smul_apply, map_smul, intervalIntegral.integral_smul] at evaluated
  have integralZero : (∫ time in (0 : ℝ)..period,
      group (-time) (bilinear neutral (group time direction))) = 0 :=
    (smul_eq_zero.mp evaluated).resolve_left (by norm_num)
  rw [quadraticResonance_apply_integral group period bilinear continuousConjugate]
  simp only [fixed, integralZero, smul_zero]

end

end EulerNonuniqueness.General
