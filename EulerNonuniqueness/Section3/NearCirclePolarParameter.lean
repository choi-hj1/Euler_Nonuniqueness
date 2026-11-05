import EulerNonuniqueness.Section3.NearCircleAngular
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Order.MonotoneContinuity

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

def nearCircleAngularOrderIso (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (nearCircleAngularLift data)
    (nearCircleAngularLift_strictMono data small)
    (nearCircleAngularLift_surjective data (small.trans (by norm_num)))

def nearCircleInverseAngle (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) : ℝ → ℝ :=
  (nearCircleAngularOrderIso data small).symm

theorem nearCircleInverseAngle_left (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) (label : ℝ) :
    nearCircleInverseAngle data small (nearCircleAngularLift data label) = label :=
  (nearCircleAngularOrderIso data small).symm_apply_apply label

theorem nearCircleInverseAngle_right (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) (angle : ℝ) :
    nearCircleAngularLift data (nearCircleInverseAngle data small angle) = angle :=
  (nearCircleAngularOrderIso data small).apply_symm_apply angle

theorem nearCircleInverseAngle_continuous (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) : Continuous (nearCircleInverseAngle data small) :=
  (nearCircleAngularOrderIso data small).symm.continuous

theorem nearCircleInverseAngle_add_period (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) (angle : ℝ) :
    nearCircleInverseAngle data small (angle + 2 * Real.pi) = nearCircleInverseAngle data small angle + 2 * Real.pi := by
  apply (nearCircleAngularLift_strictMono data small).injective
  rw [nearCircleInverseAngle_right, nearCircleAngularLift_add_period, nearCircleInverseAngle_right]

def nearCircleRadialProfile (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) (angle : ℝ) : ℝ :=
  ‖data.val.1 (nearCircleInverseAngle data small angle)‖

theorem nearCircleRadialProfile_continuous (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) : Continuous (nearCircleRadialProfile data small) :=
  (data.val.1.continuous.comp (nearCircleInverseAngle_continuous data small)).norm

theorem nearCircleRadialProfile_periodic (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    Function.Periodic (nearCircleRadialProfile data small) (2 * Real.pi) := by
  intro angle
  unfold nearCircleRadialProfile
  rw [nearCircleInverseAngle_add_period, PeriodicC1HolderHalf.periodic data]

theorem nearCircleRadialProfile_lower (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) (angle : ℝ) :
    1 - ‖data - standardCircleBanach‖ ≤ nearCircleRadialProfile data small angle :=
  nearCircle_value_lower_bound data _

theorem nearCircleRadialProfile_upper (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) (angle : ℝ) :
    nearCircleRadialProfile data small angle ≤ 1 + ‖data - standardCircleBanach‖ := by
  let label := nearCircleInverseAngle data small angle
  have estimate := norm_sub_norm_le (data.val.1 label) (standardCircle label)
  rw [standardCircle_norm] at estimate
  have difference_bound := PeriodicC1HolderHalf.value_bound (data - standardCircleBanach) label
  change ‖data.val.1 label - standardCircle label‖ ≤ ‖data - standardCircleBanach‖ at difference_bound
  change ‖data.val.1 label‖ ≤ _
  linarith

theorem nearCircle_polar_representation (data : PeriodicC1HolderHalf) (label : ℝ) :
    data.val.1 label = (‖data.val.1 label‖ : ℂ) * standardCircle (nearCircleAngularLift data label) := by
  have circle_ne : standardCircle label ≠ 0 := norm_ne_zero_iff.mp (by rw [standardCircle_norm]; norm_num)
  have ratio_norm : ‖nearCircleRatio data label‖ = ‖data.val.1 label‖ := by
    rw [nearCircleRatio, norm_div, standardCircle_norm, div_one]
  have polar := Complex.norm_mul_exp_arg_mul_I (nearCircleRatio data label)
  rw [ratio_norm, ← Complex.log_im] at polar
  change (‖data.val.1 label‖ : ℂ) * standardCircle ((Complex.log (nearCircleRatio data label)).im) =
    nearCircleRatio data label at polar
  rw [nearCircleAngularLift, standardCircle_add]
  calc
    data.val.1 label = standardCircle label * nearCircleRatio data label := by
      unfold nearCircleRatio
      field_simp
    _ = standardCircle label * ((‖data.val.1 label‖ : ℂ) * standardCircle ((Complex.log (nearCircleRatio data label)).im)) := by rw [polar]
    _ = _ := by ring

theorem nearCircleRadialProfile_parametrizes (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) (angle : ℝ) :
    data.val.1 (nearCircleInverseAngle data small angle) =
      (nearCircleRadialProfile data small angle : ℂ) * standardCircle angle := by
  have identity := nearCircle_polar_representation data (nearCircleInverseAngle data small angle)
  rwa [nearCircleInverseAngle_right] at identity

end

end EulerNonuniqueness.Paper
