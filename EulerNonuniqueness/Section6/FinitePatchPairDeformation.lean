import EulerNonuniqueness.Section6.FinitePatchDeformationError
import EulerNonuniqueness.Section6.PatchReceiverDeformation

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

set_option synthInstance.maxHeartbeats 100000

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem component_deformation_on_receiver_domain (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (receiver source : Fin count)
    (sourceSmall : ‖flow.shape time source - standardCircleBanach‖ ≤ 1 / 16)
    (receiverSmall : ‖flow.shape time receiver - standardCircleBanach‖ ≤ 1 / 16)
    (sourceSeparated : 8 * configuration.radius source ≤ ‖flow.centroid time receiver - flow.centroid time source‖)
    (receiverSeparated : 4 * configuration.radius receiver ≤ ‖flow.centroid time receiver - flow.centroid time source‖)
    {position : ℂ} (member : position ∈ flow.domain time receiver) :
    ‖biotSavart (flow.componentVorticity time source) position -
        (configuration.density source * (Real.pi * configuration.radius source ^ 2)) •
          biotSavartKernel (position - flow.centroid time source)‖ ≤
      1024 * |configuration.density source * (Real.pi * configuration.radius source ^ 2)| *
        configuration.radius source ^ 2 * ‖flow.shape time source - standardCircleBanach‖ /
          (Real.pi * ‖flow.centroid time receiver - flow.centroid time source‖ ^ 3) := by
  have distancePositive : 0 < ‖flow.centroid time receiver - flow.centroid time source‖ :=
    lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 8) (configuration.radius_pos source)) sourceSeparated
  have receiverBound := (flow.domain_centroid_deformation_geometry inside receiver receiverSmall).2.1 member
  have positionBound : ‖position - flow.centroid time receiver‖ ≤ 2 * configuration.radius receiver := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using receiverBound
  obtain ⟨localPositive, localHalf, localSeparated⟩ := Section6.patch_source_receiver_ball_distance
    (sourceCenter := flow.centroid time source) (receiverCenter := flow.centroid time receiver)
    (position := position) (sourceRadius := 2 * configuration.radius source)
    (receiverRadius := 2 * configuration.radius receiver) distancePositive
    (by linarith) (by linarith) positionBound
  have error := flow.component_biotSavart_relative_deformation inside source position sourceSmall (by linarith)
  apply error.trans
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have cubed := pow_le_pow_left₀
    (by positivity : 0 ≤ ‖flow.centroid time receiver - flow.centroid time source‖ / 2) localHalf 3
  have multiplied := mul_le_mul_of_nonneg_left cubed
    (show 0 ≤ 1024 * |configuration.density source * (Real.pi * configuration.radius source ^ 2)| *
      configuration.radius source ^ 2 * ‖flow.shape time source - standardCircleBanach‖ * Real.pi by positivity)
  nlinarith

theorem external_pair_relative_deformation (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (receiver source : Fin count)
    (sourceSmall : ‖flow.shape time source - standardCircleBanach‖ ≤ 1 / 16)
    (receiverSmall : ‖flow.shape time receiver - standardCircleBanach‖ ≤ 1 / 16)
    (sourceSeparated : 8 * configuration.radius source ≤ ‖flow.centroid time receiver - flow.centroid time source‖)
    (receiverSeparated : 4 * configuration.radius receiver ≤ ‖flow.centroid time receiver - flow.centroid time source‖) :
    ‖(Real.pi * configuration.radius receiver ^ 2)⁻¹ •
        (∫ position in flow.domain time receiver, biotSavart (flow.componentVorticity time source) position) -
        (configuration.density source * (Real.pi * configuration.radius source ^ 2)) •
          biotSavartKernel (flow.centroid time receiver - flow.centroid time source)‖ ≤
      128 * |configuration.density source * (Real.pi * configuration.radius source ^ 2)| *
        (8 * configuration.radius source ^ 2 * ‖flow.shape time source - standardCircleBanach‖ +
          configuration.radius receiver ^ 2 * ‖flow.shape time receiver - standardCircleBanach‖) /
        (Real.pi * ‖flow.centroid time receiver - flow.centroid time source‖ ^ 3) := by
  let sourceMass := configuration.density source * (Real.pi * configuration.radius source ^ 2)
  let receiverArea := Real.pi * configuration.radius receiver ^ 2
  let kernel := fun position : ℂ => biotSavartKernel (position - flow.centroid time source)
  let bound := 128 * |sourceMass| *
    (8 * configuration.radius source ^ 2 * ‖flow.shape time source - standardCircleBanach‖ +
      configuration.radius receiver ^ 2 * ‖flow.shape time receiver - standardCircleBanach‖) /
    (Real.pi * ‖flow.centroid time receiver - flow.centroid time source‖ ^ 3)
  change ‖receiverArea⁻¹ •
      (∫ position in flow.domain time receiver, biotSavart (flow.componentVorticity time source) position) -
      sourceMass • biotSavartKernel (flow.centroid time receiver - flow.centroid time source)‖ ≤ bound
  have distancePositive : 0 < ‖flow.centroid time receiver - flow.centroid time source‖ :=
    lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 8) (configuration.radius_pos source)) sourceSeparated
  have receiverBounded := (flow.domain_centroid_deformation_geometry inside receiver receiverSmall).2.1
  have reverseIntegrable := Section6.integrableOn_patch_source_kernel
    (domain := flow.domain time receiver) (center := flow.centroid time receiver)
    (position := flow.centroid time source) (radius := 2 * configuration.radius receiver) receiverBounded
    (by simpa only [norm_sub_rev] using distancePositive)
    (by rw [norm_sub_rev]; linarith)
  have kernelIntegrable : IntegrableOn kernel (flow.domain time receiver) := by
    apply reverseIntegrable.neg.congr
    exact Filter.Eventually.of_forall fun position => by
      dsimp [kernel]
      rw [← Section6.biotSavartKernel_neg]
      congr 1
      abel
  have residualIntegral :
      (∫ position in flow.domain time receiver, biotSavart (flow.componentVorticity time source) position -
        sourceMass • kernel position) =
      (∫ position in flow.domain time receiver, biotSavart (flow.componentVorticity time source) position) -
        sourceMass • (∫ position in flow.domain time receiver, kernel position) := by
    rw [integral_sub (f := biotSavart (flow.componentVorticity time source))
      (g := fun position => sourceMass • kernel position)
      (flow.componentVelocity_integrableOn_domain time receiver source) (kernelIntegrable.smul sourceMass), integral_smul]
  have residualBound :
      ‖(∫ position in flow.domain time receiver, biotSavart (flow.componentVorticity time source) position) -
        sourceMass • (∫ position in flow.domain time receiver, kernel position)‖ ≤
      receiverArea * (1024 * |sourceMass| * configuration.radius source ^ 2 *
        ‖flow.shape time source - standardCircleBanach‖ /
          (Real.pi * ‖flow.centroid time receiver - flow.centroid time source‖ ^ 3)) := by
    rw [← residualIntegral]
    have finite : volume (flow.domain time receiver) < ⊤ := (flow.domain_isBounded time receiver).measure_lt_top
    have estimate := norm_integral_le_of_norm_le
      (μ := volume.restrict (flow.domain time receiver))
      (f := fun position => biotSavart (flow.componentVorticity time source) position - sourceMass • kernel position)
      (g := fun _ => 1024 * |sourceMass| * configuration.radius source ^ 2 *
        ‖flow.shape time source - standardCircleBanach‖ /
          (Real.pi * ‖flow.centroid time receiver - flow.centroid time source‖ ^ 3))
      (integrableOn_const.mpr (Or.inr finite))
      (by
        filter_upwards [ae_restrict_mem (flow.domain_isOpen time receiver).measurableSet] with position member
        exact flow.component_deformation_on_receiver_domain inside receiver source sourceSmall receiverSmall
          sourceSeparated receiverSeparated member)
    have areaIdentity : (volume.restrict (flow.domain time receiver)).real univ = receiverArea := by
      simpa only [Measure.real, Measure.restrict_apply_univ] using flow.domain_area inside receiver
    rw [integral_const, areaIdentity, smul_eq_mul] at estimate
    exact estimate
  have trapping := flow.domain_nearCircle_trapping time receiver
  have receiverEstimate := Section6.patch_receiver_relative_deformation_bound
    (domain := flow.domain time receiver) (radius := configuration.radius receiver)
    (epsilon := ‖flow.shape time receiver - standardCircleBanach‖)
    (flow.domain_isOpen time receiver).measurableSet (configuration.center receiver) (flow.centroid time receiver)
    (flow.centroid time source) (configuration.radius_pos receiver)
    (norm_nonneg (flow.shape time receiver - standardCircleBanach)) receiverSmall trapping.1 trapping.2
    (flow.domain_area inside receiver) (flow.domain_centroid_centered_integral inside receiver) receiverSeparated
  have weightedReceiver :
      ‖sourceMass • (∫ position in flow.domain time receiver, kernel position) -
          (sourceMass * receiverArea) • biotSavartKernel (flow.centroid time receiver - flow.centroid time source)‖ ≤
        |sourceMass| * (128 * receiverArea * configuration.radius receiver ^ 2 *
          ‖flow.shape time receiver - standardCircleBanach‖ /
            (Real.pi * ‖flow.centroid time receiver - flow.centroid time source‖ ^ 3)) := by
    rw [mul_smul sourceMass receiverArea, ← smul_sub, norm_smul]
    simpa only [Real.norm_eq_abs] using mul_le_mul_of_nonneg_left receiverEstimate (norm_nonneg sourceMass)
  have unnormalized :
      ‖(∫ position in flow.domain time receiver, biotSavart (flow.componentVorticity time source) position) -
        (sourceMass * receiverArea) • biotSavartKernel (flow.centroid time receiver - flow.centroid time source)‖ ≤
      receiverArea * bound := by
    apply (norm_sub_le_norm_sub_add_norm_sub
      (∫ position in flow.domain time receiver, biotSavart (flow.componentVorticity time source) position)
      (sourceMass • (∫ position in flow.domain time receiver, kernel position))
      ((sourceMass * receiverArea) • biotSavartKernel (flow.centroid time receiver - flow.centroid time source))).trans
    apply (add_le_add residualBound weightedReceiver).trans_eq
    dsimp only [bound]
    ring
  have areaPositive : 0 < receiverArea := mul_pos Real.pi_pos (sq_pos_of_pos (configuration.radius_pos receiver))
  have normalized := mul_le_mul_of_nonneg_left unnormalized (inv_nonneg.mpr areaPositive.le)
  have cancellation : receiverArea⁻¹ * (sourceMass * receiverArea) = sourceMass := by
    field_simp
  rw [← Real.norm_of_nonneg (inv_nonneg.mpr areaPositive.le), ← norm_smul,
    smul_sub, smul_smul, cancellation] at normalized
  rw [Real.norm_of_nonneg (inv_nonneg.mpr areaPositive.le)] at normalized
  exact normalized.trans_eq (by rw [← mul_assoc, inv_mul_cancel₀ areaPositive.ne', one_mul])

theorem centroidPointResidual_relative_deformation_bound (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration)
    (small : ∀ index, ‖flow.shape time index - standardCircleBanach‖ ≤ 1 / 16)
    (receiver : Fin count)
    (separated : ∀ source, source ≠ receiver →
      8 * configuration.radius source ≤ ‖flow.centroid time receiver - flow.centroid time source‖ ∧
      4 * configuration.radius receiver ≤ ‖flow.centroid time receiver - flow.centroid time source‖) :
    ‖flow.centroidPointResidual time receiver‖ ≤
      ∑ source ∈ Finset.univ.erase receiver,
        128 * |configuration.density source * (Real.pi * configuration.radius source ^ 2)| *
          (8 * configuration.radius source ^ 2 * ‖flow.shape time source - standardCircleBanach‖ +
            configuration.radius receiver ^ 2 * ‖flow.shape time receiver - standardCircleBanach‖) /
          (Real.pi * ‖flow.centroid time receiver - flow.centroid time source‖ ^ 3) := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro source member
  have different : source ≠ receiver := (Finset.mem_erase.mp member).1
  exact flow.external_pair_relative_deformation inside receiver source (small source) (small receiver)
    (separated source different).1 (separated source different).2

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
