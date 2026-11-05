import EulerNonuniqueness.Section3.C1ContourEvaluation
import EulerNonuniqueness.Section3.NearCirclePolarParameter

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

theorem continuous_nearCircleAngularLift_joint {X : Type*} [TopologicalSpace X]
    (shape : X → PeriodicC1HolderHalf) (shape_continuous : Continuous shape)
    (small : ∀ parameter, ‖shape parameter - standardCircleBanach‖ < 1 / 3) :
    Continuous (fun pair : X × ℝ => nearCircleAngularLift (shape pair.1) pair.2) := by
  have circle_continuous : Continuous standardCircle := standardCircleBanach.val.1.continuous
  have ratio_continuous : Continuous (fun pair : X × ℝ => nearCircleRatio (shape pair.1) pair.2) :=
    (continuous_contour_value_joint shape shape_continuous).div (circle_continuous.comp continuous_snd)
      (fun pair => norm_ne_zero_iff.mp (by rw [standardCircle_norm]; norm_num))
  have log_continuous : Continuous (fun pair : X × ℝ => Complex.log (nearCircleRatio (shape pair.1) pair.2)) :=
    continuous_iff_continuousAt.mpr fun pair => ratio_continuous.continuousAt.clog
      (nearCircleRatio_mem_slitPlane (shape pair.1) ((small pair.1).trans (by norm_num)) pair.2)
  exact continuous_snd.add (Complex.continuous_im.comp log_continuous)

theorem continuous_nearCircleInverseAngle_joint {X : Type*} [TopologicalSpace X]
    (shape : X → PeriodicC1HolderHalf) (shape_continuous : Continuous shape)
    (small : ∀ parameter, ‖shape parameter - standardCircleBanach‖ < 1 / 3) :
    Continuous (fun pair : X × ℝ => nearCircleInverseAngle (shape pair.1) (small pair.1) pair.2) := by
  have angular_continuous := continuous_nearCircleAngularLift_joint shape shape_continuous small
  apply continuous_iff_continuousAt.mpr
  intro point
  apply tendsto_order.mpr
  constructor
  · intro lower lower_lt
    have lifted : nearCircleAngularLift (shape point.1) lower < point.2 := by
      have inequality := (nearCircleAngularLift_strictMono (shape point.1) (small point.1)) lower_lt
      rwa [nearCircleInverseAngle_right] at inequality
    have neighborhood : {pair : X × ℝ | nearCircleAngularLift (shape pair.1) lower < pair.2} ∈ 𝓝 point :=
      (isOpen_lt (angular_continuous.comp (continuous_fst.prodMk continuous_const)) continuous_snd).mem_nhds lifted
    filter_upwards [neighborhood] with pair bound
    apply (nearCircleAngularLift_strictMono (shape pair.1) (small pair.1)).lt_iff_lt.mp
    rwa [nearCircleInverseAngle_right]
  · intro upper upper_lt
    have lifted : point.2 < nearCircleAngularLift (shape point.1) upper := by
      have inequality := (nearCircleAngularLift_strictMono (shape point.1) (small point.1)) upper_lt
      rwa [nearCircleInverseAngle_right] at inequality
    have neighborhood : {pair : X × ℝ | pair.2 < nearCircleAngularLift (shape pair.1) upper} ∈ 𝓝 point :=
      (isOpen_lt continuous_snd (angular_continuous.comp (continuous_fst.prodMk continuous_const))).mem_nhds lifted
    filter_upwards [neighborhood] with pair bound
    apply (nearCircleAngularLift_strictMono (shape pair.1) (small pair.1)).lt_iff_lt.mp
    rwa [nearCircleInverseAngle_right]

theorem continuous_nearCircleRadialProfile_joint {X : Type*} [TopologicalSpace X]
    (shape : X → PeriodicC1HolderHalf) (shape_continuous : Continuous shape)
    (small : ∀ parameter, ‖shape parameter - standardCircleBanach‖ < 1 / 3) :
    Continuous (fun pair : X × ℝ => nearCircleRadialProfile (shape pair.1) (small pair.1) pair.2) := by
  exact ((continuous_contour_value_joint shape shape_continuous).comp
    (continuous_fst.prodMk (continuous_nearCircleInverseAngle_joint shape shape_continuous small))).norm

end

end EulerNonuniqueness.Paper
