import EulerNonuniqueness.Section6.PatchReceiverComparison
import EulerNonuniqueness.Section6.PatchSourceBallComparison
import EulerNonuniqueness.Section6.PatchExternalCentroidLaw

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Section6

theorem patch_pair_centroid_comparison {sourceDomain receiverDomain : Set ℂ}
    (sourceMeasurable : MeasurableSet sourceDomain) (receiverMeasurable : MeasurableSet receiverDomain)
    {sourceCenter receiverCenter : ℂ} {sourceRadius receiverRadius : ℝ}
    (sourceBounded : sourceDomain ⊆ Metric.closedBall sourceCenter sourceRadius)
    (receiverBounded : receiverDomain ⊆ Metric.closedBall receiverCenter receiverRadius)
    (sourceCentroid : (∫ source in sourceDomain, source - sourceCenter) = 0)
    (receiverCentroid : (∫ position in receiverDomain, position - receiverCenter) = 0)
    (distancePositive : 0 < ‖receiverCenter - sourceCenter‖)
    (sourceSmall : 4 * sourceRadius ≤ ‖receiverCenter - sourceCenter‖)
    (receiverSmall : 2 * receiverRadius ≤ ‖receiverCenter - sourceCenter‖) (density : ℝ) :
    ‖(∫ position in receiverDomain, biotSavart (sourceDomain.indicator (fun _ => density)) position) -
        (density * volume.real sourceDomain * volume.real receiverDomain) •
          biotSavartKernel (receiverCenter - sourceCenter)‖ ≤
      |density| * volume.real sourceDomain * volume.real receiverDomain *
        (8 * sourceRadius ^ 2 + receiverRadius ^ 2) /
          (Real.pi * ‖receiverCenter - sourceCenter‖ ^ 3) := by
  let mass := density * volume.real sourceDomain
  let kernel := fun position : ℂ => biotSavartKernel (position - sourceCenter)
  have sourceFinite : volume sourceDomain < ⊤ :=
    lt_of_le_of_lt (measure_mono sourceBounded) measure_closedBall_lt_top
  have receiverFinite : volume receiverDomain < ⊤ :=
    lt_of_le_of_lt (measure_mono receiverBounded) measure_closedBall_lt_top
  have sourceIntegrable : Integrable (sourceDomain.indicator (fun _ => density)) :=
    (integrable_indicator_iff sourceMeasurable).mpr (integrableOn_const.mpr (Or.inr sourceFinite))
  have sourceMember : MemLp (sourceDomain.indicator (fun _ => density)) (ENNReal.ofReal (4 : ℝ)) volume :=
    memLp_indicator_const _ sourceMeasurable _ (Or.inr sourceFinite.ne)
  have velocityIntegrable := integrableOn_biotSavart_of_L1_L4_finite
    sourceIntegrable sourceMember receiverFinite
  have reverseIntegrable := integrableOn_patch_source_kernel (domain := receiverDomain)
    (center := receiverCenter) (position := sourceCenter) (radius := receiverRadius)
    receiverBounded (by simpa only [norm_sub_rev] using distancePositive)
    (by simpa only [norm_sub_rev] using receiverSmall)
  have kernelIntegrable : IntegrableOn kernel receiverDomain := by
    apply reverseIntegrable.neg.congr
    exact Filter.Eventually.of_forall fun position => by
      dsimp [kernel]
      rw [← biotSavartKernel_neg]
      congr 1
      abel
  have residualIntegral :
      (∫ position in receiverDomain, biotSavart (sourceDomain.indicator (fun _ => density)) position -
        mass • kernel position) =
      (∫ position in receiverDomain, biotSavart (sourceDomain.indicator (fun _ => density)) position) -
        mass • (∫ position in receiverDomain, kernel position) := by
    rw [integral_sub (f := biotSavart (sourceDomain.indicator (fun _ => density)))
      (g := fun position => mass • kernel position) velocityIntegrable (kernelIntegrable.smul mass), integral_smul]
  have residualBound :
      ‖(∫ position in receiverDomain, biotSavart (sourceDomain.indicator (fun _ => density)) position) -
        mass • (∫ position in receiverDomain, kernel position)‖ ≤
      volume.real receiverDomain *
        (8 * |density| * volume.real sourceDomain * sourceRadius ^ 2 /
          (Real.pi * ‖receiverCenter - sourceCenter‖ ^ 3)) := by
    rw [← residualIntegral]
    have estimate := norm_integral_le_of_norm_le
      (μ := volume.restrict receiverDomain)
      (f := fun position => biotSavart (sourceDomain.indicator (fun _ => density)) position - mass • kernel position)
      (g := fun _ => 8 * |density| * volume.real sourceDomain * sourceRadius ^ 2 /
        (Real.pi * ‖receiverCenter - sourceCenter‖ ^ 3))
      (integrableOn_const.mpr (Or.inr receiverFinite))
      (by
        filter_upwards [ae_restrict_mem receiverMeasurable] with position member
        exact biotSavart_patch_receiver_ball_comparison sourceMeasurable sourceBounded sourceCentroid
          distancePositive sourceSmall receiverSmall
          (by simpa [dist_eq_norm] using receiverBounded member) density)
    simpa only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ] using estimate
  have receiverEstimate := patch_receiver_centroid_comparison (domain := receiverDomain)
    (center := receiverCenter) (sourceCenter := sourceCenter) (radius := receiverRadius)
    receiverMeasurable receiverBounded
    receiverCentroid distancePositive receiverSmall
  have weightedReceiver :
      ‖mass • (∫ position in receiverDomain, kernel position) -
          (density * volume.real sourceDomain * volume.real receiverDomain) •
            biotSavartKernel (receiverCenter - sourceCenter)‖ ≤
        |density| * volume.real sourceDomain *
          (volume.real receiverDomain * receiverRadius ^ 2 /
            (Real.pi * ‖receiverCenter - sourceCenter‖ ^ 3)) := by
    change ‖mass • (∫ position in receiverDomain, kernel position) -
      (mass * volume.real receiverDomain) • biotSavartKernel (receiverCenter - sourceCenter)‖ ≤ _
    rw [mul_smul mass (volume.real receiverDomain), ← smul_sub, norm_smul]
    have estimate := mul_le_mul_of_nonneg_left receiverEstimate (norm_nonneg mass)
    simpa only [mass, kernel, Real.norm_eq_abs, abs_mul, abs_of_nonneg measureReal_nonneg] using estimate
  apply (norm_sub_le_norm_sub_add_norm_sub
    (∫ position in receiverDomain, biotSavart (sourceDomain.indicator (fun _ => density)) position)
    (mass • (∫ position in receiverDomain, kernel position))
    ((density * volume.real sourceDomain * volume.real receiverDomain) •
      biotSavartKernel (receiverCenter - sourceCenter))).trans
  apply (add_le_add residualBound weightedReceiver).trans_eq
  ring

end EulerNonuniqueness.Section6
