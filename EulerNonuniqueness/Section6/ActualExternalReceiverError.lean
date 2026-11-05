import EulerNonuniqueness.Section6.FinitePatchPairDeformation
import EulerNonuniqueness.Section6.PatchCrossInteraction

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

set_option synthInstance.maxHeartbeats 100000

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem component_cross_weighted_integral_zero (flow : FiniteLiteralPatchFlow configuration)
    (time : ℝ) (first second : Fin count) :
    configuration.density first • (∫ position in flow.domain time first,
        biotSavart (flow.componentVorticity time second) position) +
      configuration.density second • (∫ position in flow.domain time second,
        biotSavart (flow.componentVorticity time first) position) = 0 := by
  obtain ⟨radius, _, bounded⟩ := ((flow.domain_isBounded time first).union
    (flow.domain_isBounded time second)).exists_pos_norm_le
  exact Section6.integral_patch_cross_interaction_density
    (flow.domain_isOpen time first).measurableSet (flow.domain_isOpen time second).measurableSet
    (show flow.domain time first ⊆ Metric.closedBall 0 radius from fun position member => by
      simpa using bounded position (Or.inl member))
    (show flow.domain time second ⊆ Metric.closedBall 0 radius from fun position member => by
      simpa using bounded position (Or.inr member))
    (configuration.density first) (configuration.density second)

theorem component_velocity_reverse_integral (flow : FiniteLiteralPatchFlow configuration)
    (time : ℝ) (source : Fin count) (position : ℂ) :
    biotSavart (flow.componentVorticity time source) position =
      -(configuration.density source) •
        (∫ location in flow.domain time source, biotSavartKernel (location - position)) := by
  change biotSavart ((flow.domain time source).indicator (fun _ => configuration.density source)) position = _
  rw [Section6.biotSavart_indicator_density_integral (flow.domain_isOpen time source).measurableSet]
  have flip : (∫ location in flow.domain time source, biotSavartKernel (position - location)) =
      -(∫ location in flow.domain time source, biotSavartKernel (location - position)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun location => by
      dsimp only
      rw [← Section6.biotSavartKernel_neg]
      congr 1
      abel
  rw [flip, smul_neg, neg_smul]

theorem component_actual_receiver_averaging_bound_of_trapping (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (receiver source : Fin count)
    (densityNonzero : configuration.density receiver ≠ 0)
    (receiverCenter : ℂ) {deformation : ℝ} (deformationNonnegative : 0 ≤ deformation)
    (deformationSmall : deformation ≤ 1 / 16)
    (receiverLower : Metric.ball receiverCenter (configuration.radius receiver * (1 - deformation)) ⊆ flow.domain time receiver)
    (receiverUpper : flow.domain time receiver ⊆ Metric.ball receiverCenter (configuration.radius receiver * (1 + deformation)))
    (sourceBounded : flow.domain time source ⊆ Metric.closedBall (flow.centroid time source) (2 * configuration.radius source))
    (receiverSeparated : 8 * configuration.radius receiver ≤ ‖flow.centroid time receiver - flow.centroid time source‖)
    (sourceSeparated : 4 * configuration.radius source ≤ ‖flow.centroid time receiver - flow.centroid time source‖) :
    ‖(Real.pi * configuration.radius receiver ^ 2)⁻¹ •
        (∫ position in flow.domain time receiver, biotSavart (flow.componentVorticity time source) position) -
        biotSavart (flow.componentVorticity time source) (flow.centroid time receiver)‖ ≤
      1024 * |configuration.density source * (Real.pi * configuration.radius source ^ 2)| *
        configuration.radius receiver ^ 2 * deformation /
        (Real.pi * ‖flow.centroid time receiver - flow.centroid time source‖ ^ 3) := by
  let receiverArea := Real.pi * configuration.radius receiver ^ 2
  let sourceArea := Real.pi * configuration.radius source ^ 2
  let receiverMass := configuration.density receiver * receiverArea
  let distance := ‖flow.centroid time receiver - flow.centroid time source‖
  let residual := fun position : ℂ => biotSavart (flow.componentVorticity time receiver) position -
    receiverMass • biotSavartKernel (position - flow.centroid time receiver)
  have receiverAreaPositive : 0 < receiverArea := mul_pos Real.pi_pos (sq_pos_of_pos (configuration.radius_pos receiver))
  have sourceAreaNonnegative : 0 ≤ sourceArea := by dsimp only [sourceArea]; positivity
  have receiverMassNonzero : receiverMass ≠ 0 := mul_ne_zero densityNonzero receiverAreaPositive.ne'
  have distancePositive : 0 < distance := lt_of_lt_of_le
    (mul_pos (by norm_num : (0 : ℝ) < 8) (configuration.radius_pos receiver)) receiverSeparated
  have reverseKernel := Section6.integrableOn_patch_source_kernel
    (domain := flow.domain time source) (center := flow.centroid time source)
    (position := flow.centroid time receiver) (radius := 2 * configuration.radius source)
    sourceBounded distancePositive (by linarith)
  have kernelIntegrable : IntegrableOn
      (fun position => biotSavartKernel (position - flow.centroid time receiver)) (flow.domain time source) := by
    apply reverseKernel.neg.congr
    exact Filter.Eventually.of_forall fun position => by
      change -biotSavartKernel (flow.centroid time receiver - position) =
        biotSavartKernel (position - flow.centroid time receiver)
      rw [← Section6.biotSavartKernel_neg]
      congr 1
      abel
  have integralResidual : (∫ position in flow.domain time source, residual position) =
      (∫ position in flow.domain time source, biotSavart (flow.componentVorticity time receiver) position) -
        receiverMass • (∫ position in flow.domain time source, biotSavartKernel (position - flow.centroid time receiver)) := by
    rw [integral_sub (f := biotSavart (flow.componentVorticity time receiver))
      (g := fun position => receiverMass • biotSavartKernel (position - flow.centroid time receiver))
      (flow.componentVelocity_integrableOn_domain time source receiver) (kernelIntegrable.smul receiverMass), integral_smul]
  have residualBound : ‖∫ position in flow.domain time source, residual position‖ ≤
      sourceArea * (1024 * |receiverMass| * configuration.radius receiver ^ 2 *
        deformation / (Real.pi * distance ^ 3)) := by
    have estimate := norm_integral_le_of_norm_le
      (μ := volume.restrict (flow.domain time source)) (f := residual)
      (g := fun _ => 1024 * |receiverMass| * configuration.radius receiver ^ 2 *
        deformation / (Real.pi * distance ^ 3))
      (integrableOn_const.mpr (Or.inr (flow.domain_isBounded time source).measure_lt_top)) (by
        filter_upwards [ae_restrict_mem (flow.domain_isOpen time source).measurableSet] with position member
        have positionBound : ‖position - flow.centroid time source‖ ≤ 2 * configuration.radius source := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using sourceBounded member
        have triangle : distance ≤ ‖position - flow.centroid time source‖ +
            ‖position - flow.centroid time receiver‖ := by
          have estimate := norm_sub_le (position - flow.centroid time source) (position - flow.centroid time receiver)
          have identity : (position - flow.centroid time source) - (position - flow.centroid time receiver) =
              flow.centroid time receiver - flow.centroid time source := by abel
          rw [identity] at estimate
          exact estimate
        have localHalf : distance / 2 ≤ ‖position - flow.centroid time receiver‖ := by linarith
        have localPositive : 0 < ‖position - flow.centroid time receiver‖ := by linarith
        have control := Section6.biotSavart_patch_relative_deformation_bound
          (flow.domain_isOpen time receiver).measurableSet receiverCenter (flow.centroid time receiver) position
          (configuration.radius_pos receiver) deformationNonnegative deformationSmall receiverLower receiverUpper
          (flow.domain_area inside receiver) (flow.domain_centroid_centered_integral inside receiver)
          (by linarith : 4 * configuration.radius receiver ≤ ‖position - flow.centroid time receiver‖)
          (configuration.density receiver)
        apply control.trans
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        have cubed := pow_le_pow_left₀ (by positivity : 0 ≤ distance / 2) localHalf 3
        have multiplied := mul_le_mul_of_nonneg_left cubed
          (show 0 ≤ 1024 * |receiverMass| * configuration.radius receiver ^ 2 * deformation * Real.pi by positivity)
        nlinarith)
    have area : (volume.restrict (flow.domain time source)).real univ = sourceArea := by
      simpa only [Measure.real, Measure.restrict_apply_univ] using flow.domain_area inside source
    simpa only [integral_const, area, smul_eq_mul] using estimate
  have weightedIdentity : receiverMass •
      (receiverArea⁻¹ • (∫ position in flow.domain time receiver, biotSavart (flow.componentVorticity time source) position) -
        biotSavart (flow.componentVorticity time source) (flow.centroid time receiver)) =
      -(configuration.density source) • (∫ position in flow.domain time source, residual position) := by
    have normalization : receiverMass * receiverArea⁻¹ = configuration.density receiver := by
      dsimp only [receiverMass]
      field_simp
    have cross := eq_neg_of_add_eq_zero_left (flow.component_cross_weighted_integral_zero time receiver source)
    rw [smul_sub, smul_smul, normalization, cross,
      flow.component_velocity_reverse_integral time source (flow.centroid time receiver), integralResidual]
    simp only [Complex.real_smul, Complex.ofReal_neg]
    ring
  have weightedBound := mul_le_mul_of_nonneg_left residualBound (abs_nonneg (configuration.density source))
  have normIdentity := congrArg norm weightedIdentity
  simp only [norm_smul, Real.norm_eq_abs, abs_neg] at normIdentity
  rw [← normIdentity] at weightedBound
  apply (mul_le_mul_left (abs_pos.mpr receiverMassNonzero)).mp
  apply weightedBound.trans_eq
  rw [abs_mul (configuration.density source) sourceArea, abs_of_nonneg sourceAreaNonnegative]
  ring

theorem component_actual_receiver_averaging_bound (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (receiver source : Fin count)
    (densityNonzero : configuration.density receiver ≠ 0)
    (receiverSmall : ‖flow.shape time receiver - standardCircleBanach‖ ≤ 1 / 16)
    (sourceSmall : ‖flow.shape time source - standardCircleBanach‖ ≤ 1 / 16)
    (receiverSeparated : 8 * configuration.radius receiver ≤ ‖flow.centroid time receiver - flow.centroid time source‖)
    (sourceSeparated : 4 * configuration.radius source ≤ ‖flow.centroid time receiver - flow.centroid time source‖) :
    ‖(Real.pi * configuration.radius receiver ^ 2)⁻¹ •
        (∫ position in flow.domain time receiver, biotSavart (flow.componentVorticity time source) position) -
        biotSavart (flow.componentVorticity time source) (flow.centroid time receiver)‖ ≤
      1024 * |configuration.density source * (Real.pi * configuration.radius source ^ 2)| *
        configuration.radius receiver ^ 2 * ‖flow.shape time receiver - standardCircleBanach‖ /
        (Real.pi * ‖flow.centroid time receiver - flow.centroid time source‖ ^ 3) := by
  have trapping := flow.domain_nearCircle_trapping time receiver
  exact flow.component_actual_receiver_averaging_bound_of_trapping inside receiver source densityNonzero
    (configuration.center receiver) (norm_nonneg (flow.shape time receiver - standardCircleBanach)) receiverSmall
    trapping.1 trapping.2 (flow.domain_centroid_deformation_geometry inside source sourceSmall).2.1
    receiverSeparated sourceSeparated

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
