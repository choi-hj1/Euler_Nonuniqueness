import EulerNonuniqueness.Section6.PaperPatchCentroidAlgebra
import EulerNonuniqueness.Section6.PatchCrossInteraction

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.patch_actual_receiver_averaging_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (receiverIndex sourceIndex : Fin count) (receiver source : Fin 4)
    (control : BoundaryCloseToCircle scales motion time receiverIndex receiver deformation)
    (deformationNonnegative : 0 ≤ deformation) (deformationSmall : deformation ≤ 1 / 16)
    (sourceBounded : motion.domain time sourceIndex source ⊆
      Metric.closedBall (patchCentroid motion time sourceIndex source) (2 * scales.radius (sourceIndex.val + 1)))
    (receiverSeparated : 8 * scales.radius (receiverIndex.val + 1) ≤
      ‖patchCentroid motion time receiverIndex receiver - patchCentroid motion time sourceIndex source‖)
    (sourceSeparated : 4 * scales.radius (sourceIndex.val + 1) ≤
      ‖patchCentroid motion time receiverIndex receiver - patchCentroid motion time sourceIndex source‖) :
    ‖patchAverageVelocity scales motion time receiverIndex receiver
        (biotSavart (patchDensity scales motion time sourceIndex source)) -
      biotSavart (patchDensity scales motion time sourceIndex source) (patchCentroid motion time receiverIndex receiver)‖ ≤
      1024 * scales.circulation (sourceIndex.val + 1) * scales.radius (receiverIndex.val + 1) ^ 2 * deformation /
        (Real.pi * ‖patchCentroid motion time receiverIndex receiver - patchCentroid motion time sourceIndex source‖ ^ 3) := by
  let receiverDomain := motion.domain time receiverIndex receiver
  let sourceDomain := motion.domain time sourceIndex source
  let receiverCenter := patchCentroid motion time receiverIndex receiver
  let sourceCenter := patchCentroid motion time sourceIndex source
  let receiverArea := Real.pi * scales.radius (receiverIndex.val + 1) ^ 2
  let sourceArea := Real.pi * scales.radius (sourceIndex.val + 1) ^ 2
  let sourceDensity := patchSign source * scales.amplitude * scales.omega (sourceIndex.val + 1) ^ 4
  let receiverVorticity : Vorticity := receiverDomain.indicator (fun _ => 1)
  let residual := fun position => biotSavart receiverVorticity position -
    receiverArea • biotSavartKernel (position - receiverCenter)
  let distance := ‖receiverCenter - sourceCenter‖
  have receiverProperties := evolution.2.2.2.1 time inside receiverIndex receiver
  have sourceProperties := evolution.2.2.2.1 time inside sourceIndex source
  have receiverRadiusPositive := scales.radius_pos amplitudePositive frequencyPositive ratioPositive (receiverIndex.val + 1)
  have receiverAreaPositive : 0 < receiverArea := by dsimp only [receiverArea]; positivity
  have receiverAreaEquation : volume.real receiverDomain = receiverArea := by
    rw [Measure.real, receiverProperties.2.2.1, ENNReal.toReal_ofReal receiverAreaPositive.le]
  have sourceAreaEquation : volume.real sourceDomain = sourceArea := by
    rw [Measure.real, sourceProperties.2.2.1, ENNReal.toReal_ofReal (by positivity)]
  have distancePositive : 0 < distance := lt_of_lt_of_le (by positivity : 0 < 8 * scales.radius (receiverIndex.val + 1)) receiverSeparated
  have trapping := evolution.domain_radial_trapping inside receiverIndex receiver control deformationNonnegative
    (by linarith) receiverRadiusPositive
  have receiverIntegrable : Integrable receiverVorticity :=
    (integrable_indicator_iff receiverProperties.1.measurableSet).mpr
      (integrableOn_const.mpr (Or.inr receiverProperties.2.1.measure_lt_top))
  have receiverMemLp : MemLp receiverVorticity (ENNReal.ofReal (4 : ℝ)) volume :=
    memLp_indicator_const _ receiverProperties.1.measurableSet _ (Or.inr receiverProperties.2.1.measure_lt_top.ne)
  have receiverVelocityIntegrable : IntegrableOn (biotSavart receiverVorticity) sourceDomain :=
    Section6.integrableOn_biotSavart_of_L1_L4_finite receiverIntegrable receiverMemLp sourceProperties.2.1.measure_lt_top
  have kernelIntegrable : IntegrableOn (fun position => biotSavartKernel (position - receiverCenter)) sourceDomain := by
    have reverse := Section6.integrableOn_patch_source_kernel (domain := sourceDomain)
      (center := sourceCenter) (position := receiverCenter) (radius := 2 * scales.radius (sourceIndex.val + 1))
      sourceBounded distancePositive (by linarith)
    apply reverse.neg.congr
    exact Filter.Eventually.of_forall fun position => by
      change -biotSavartKernel (receiverCenter - position) = biotSavartKernel (position - receiverCenter)
      rw [← Section6.biotSavartKernel_neg]
      congr 1
      abel
  have integralResidual : (∫ position in sourceDomain, residual position) =
      (∫ position in sourceDomain, biotSavart receiverVorticity position) -
        receiverArea • (∫ position in sourceDomain, biotSavartKernel (position - receiverCenter)) := by
    rw [integral_sub (f := biotSavart receiverVorticity)
      (g := fun position => receiverArea • biotSavartKernel (position - receiverCenter))
      receiverVelocityIntegrable (kernelIntegrable.smul receiverArea), integral_smul]
  have residualBound : ‖∫ position in sourceDomain, residual position‖ ≤
      sourceArea * (1024 * receiverArea * scales.radius (receiverIndex.val + 1) ^ 2 * deformation /
        (Real.pi * distance ^ 3)) := by
    have estimate := norm_integral_le_of_norm_le (μ := volume.restrict sourceDomain) (f := residual)
      (g := fun _ : ℂ => 1024 * receiverArea * scales.radius (receiverIndex.val + 1) ^ 2 * deformation /
        (Real.pi * distance ^ 3)) (integrableOn_const.mpr (Or.inr sourceProperties.2.1.measure_lt_top)) (by
        filter_upwards [ae_restrict_mem sourceProperties.1.measurableSet] with position member
        have positionBound : ‖position - sourceCenter‖ ≤ 2 * scales.radius (sourceIndex.val + 1) := by
          simpa only [Metric.mem_closedBall, dist_eq_norm] using sourceBounded member
        have triangle : distance ≤ ‖position - sourceCenter‖ + ‖position - receiverCenter‖ := by
          have estimate := norm_sub_le (position - sourceCenter) (position - receiverCenter)
          have identity : position - sourceCenter - (position - receiverCenter) = receiverCenter - sourceCenter := by abel
          rw [identity] at estimate
          exact estimate
        have half : distance / 2 ≤ ‖position - receiverCenter‖ := by linarith
        have localPositive : 0 < ‖position - receiverCenter‖ := by linarith
        have estimate := Section6.biotSavart_patch_relative_deformation_bound receiverProperties.1.measurableSet
          receiverCenter receiverCenter position receiverRadiusPositive deformationNonnegative deformationSmall
          trapping.1 trapping.2 receiverAreaEquation
          (evolution.patch_centroid_centered_integral_zero inside receiverIndex receiver)
          (by linarith : 4 * scales.radius (receiverIndex.val + 1) ≤ ‖position - receiverCenter‖) 1
        simp only [one_mul] at estimate
        change ‖residual position‖ ≤ 128 * |receiverArea| * scales.radius (receiverIndex.val + 1) ^ 2 * deformation /
          (Real.pi * ‖position - receiverCenter‖ ^ 3) at estimate
        rw [abs_of_pos receiverAreaPositive] at estimate
        apply estimate.trans
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        have cubed := pow_le_pow_left₀ (by positivity : 0 ≤ distance / 2) half 3
        have multiplied := mul_le_mul_of_nonneg_left cubed
          (show 0 ≤ 1024 * receiverArea * scales.radius (receiverIndex.val + 1) ^ 2 * deformation * Real.pi by positivity)
        nlinarith)
    have restrictedArea : (volume.restrict sourceDomain).real univ = sourceArea := by
      simpa only [Measure.real, Measure.restrict_apply_univ] using sourceAreaEquation
    simpa only [integral_const, restrictedArea, smul_eq_mul] using estimate
  obtain ⟨radius, _, bounded⟩ := (receiverProperties.2.1.union sourceProperties.2.1).exists_pos_norm_le
  have cross := Section6.integral_patch_cross_interaction_density receiverProperties.1.measurableSet sourceProperties.1.measurableSet
    (show receiverDomain ⊆ Metric.closedBall 0 radius from fun position member => by simpa using bounded position (Or.inl member))
    (show sourceDomain ⊆ Metric.closedBall 0 radius from fun position member => by simpa using bounded position (Or.inr member))
    1 sourceDensity
  simp only [one_smul] at cross
  change (∫ position in receiverDomain, biotSavart (patchDensity scales motion time sourceIndex source) position) +
    sourceDensity • (∫ position in sourceDomain, biotSavart receiverVorticity position) = 0 at cross
  have reverseVelocity : biotSavart (patchDensity scales motion time sourceIndex source) receiverCenter =
      -sourceDensity • (∫ position in sourceDomain, biotSavartKernel (position - receiverCenter)) := by
    change biotSavart (sourceDomain.indicator (fun _ => sourceDensity)) receiverCenter = _
    rw [Section6.biotSavart_indicator_density_integral sourceProperties.1.measurableSet]
    have flip : (∫ position in sourceDomain, biotSavartKernel (receiverCenter - position)) =
        -(∫ position in sourceDomain, biotSavartKernel (position - receiverCenter)) := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun position => by
        change biotSavartKernel (receiverCenter - position) = -biotSavartKernel (position - receiverCenter)
        rw [← Section6.biotSavartKernel_neg]
        congr 1
        abel
    rw [flip, smul_neg, neg_smul]
  have weightedIdentity : receiverArea •
      (patchAverageVelocity scales motion time receiverIndex receiver (biotSavart (patchDensity scales motion time sourceIndex source)) -
        biotSavart (patchDensity scales motion time sourceIndex source) receiverCenter) =
      -sourceDensity • (∫ position in sourceDomain, residual position) := by
    have normalization : receiverArea * receiverArea⁻¹ = 1 := mul_inv_cancel₀ receiverAreaPositive.ne'
    rw [patchAverageVelocity, smul_sub, smul_smul, normalization, one_smul,
      eq_neg_of_add_eq_zero_left cross, reverseVelocity, integralResidual]
    simp only [Complex.real_smul, Complex.ofReal_neg]
    ring
  have weightedBound := mul_le_mul_of_nonneg_left residualBound (abs_nonneg sourceDensity)
  have normIdentity := congrArg norm weightedIdentity
  simp only [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos receiverAreaPositive] at normIdentity
  rw [← normIdentity] at weightedBound
  apply (mul_le_mul_left receiverAreaPositive).mp
  apply weightedBound.trans_eq
  have mass := evolution.patch_abs_density_mul_area inside amplitudePositive frequencyPositive ratioPositive sourceIndex source
  rw [sourceAreaEquation] at mass
  calc
    _ = receiverArea * (1024 * (|sourceDensity| * sourceArea) * scales.radius (receiverIndex.val + 1) ^ 2 * deformation /
      (Real.pi * distance ^ 3)) := by ring
    _ = _ := by rw [mass]

end EulerNonuniqueness.Paper
