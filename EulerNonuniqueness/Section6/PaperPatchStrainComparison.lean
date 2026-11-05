import EulerNonuniqueness.Section6.PatchStrainDeformation
import EulerNonuniqueness.Section6.PaperPatchSourceStrain
import EulerNonuniqueness.Section6.NegativeLabelBridge

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem circulation_kernelStrain_fourPoint_sum (circulation : ℝ) (positions : FourPointConfiguration) (location : ℂ) :
    (∑ source : Fin 4, (fourPointSign source * circulation) • biotSavartKernelStrain location (positions source)) =
      fourPointExternalPointStrain (circulation / (2 * Real.pi)) positions location := by
  simp [fourPointExternalPointStrain, fourPointCauchyStrain, fourPointSign, biotSavartKernelStrain,
    Fin.sum_univ_succ, Complex.real_smul, star_div₀, star_pow]
  push_cast
  ring

theorem fourPointExternalPointStrain_negativeLabelSwap (coefficient : ℝ) (positions : FourPointConfiguration) (location : ℂ) :
    fourPointExternalPointStrain coefficient (relabelNegativePoints positions) location =
      fourPointExternalPointStrain coefficient positions location := by
  simp [fourPointExternalPointStrain, fourPointCauchyStrain, relabelNegativePoints, negativeLabelSwap,
    Equiv.swap_apply_def, fourPointSign, Fin.sum_univ_succ]
  ring_nf <;> simp

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.patch_strain_point_error_of_boundaryControl
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (patch : Fin 4) (position : ℂ)
    (control : BoundaryCloseToCircle scales motion time index patch deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16)
    (separated : 4 * scales.radius (index.val + 1) ≤ ‖position - patchCentroid motion time index patch‖) :
    ‖Section6.vorticityComplexStrain (patchDensity scales motion time index patch) position -
        (patchSign patch * scales.circulation (index.val + 1)) •
          Section6.biotSavartKernelStrain position (patchCentroid motion time index patch)‖ ≤
      1024 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
        (Real.pi * ‖position - patchCentroid motion time index patch‖ ^ 4) := by
  have properties := evolution.2.2.2.1 time inside index patch
  have radiusPositive := scales.radius_pos amplitudePositive frequencyPositive ratioPositive (index.val + 1)
  have trapping := evolution.domain_radial_trapping inside index patch control nonnegative (by linarith) radiusPositive
  have area : volume.real (motion.domain time index patch) = Real.pi * scales.radius (index.val + 1) ^ 2 := by
    rw [Measure.real, properties.2.2.1, ENNReal.toReal_ofReal (by positivity)]
  let density := patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4
  have mass : density * (Real.pi * scales.radius (index.val + 1) ^ 2) =
      patchSign patch * scales.circulation (index.val + 1) := by
    rw [← scales.patch_circulation amplitudePositive frequencyPositive ratioPositive (index.val + 1)]
    dsimp only [density]
    ring
  have absoluteMass := evolution.patch_abs_density_mul_area inside amplitudePositive frequencyPositive ratioPositive index patch
  rw [area] at absoluteMass
  have estimate := Section6.vorticityComplexStrain_patch_relative_deformation_bound properties.1.measurableSet
    (patchCentroid motion time index patch) (patchCentroid motion time index patch) position radiusPositive
    nonnegative small trapping.1 trapping.2 area
    (evolution.patch_centroid_centered_integral_zero inside index patch) separated density
  rw [abs_mul density (Real.pi * scales.radius (index.val + 1) ^ 2),
    abs_of_pos (by positivity : 0 < Real.pi * scales.radius (index.val + 1) ^ 2), absoluteMass, mass] at estimate
  exact estimate

theorem FinitePatchEvolution.quadrupole_strain_point_error
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation gap : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (position : ℂ)
    (control : ∀ patch, BoundaryCloseToCircle scales motion time index patch deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16)
    (gapPositive : 0 < gap) (radiusSmall : 4 * scales.radius (index.val + 1) ≤ gap)
    (separated : ∀ patch, gap ≤ ‖position - patchCentroid motion time index patch‖) :
    ‖Section6.vorticityComplexStrain (quadrupoleDensity scales motion time index) position -
        Section6.fourPointExternalPointStrain (scales.circulation (index.val + 1) / (2 * Real.pi))
          (fun patch => patchCentroid motion time index patch) position‖ ≤
      4096 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
        (Real.pi * gap ^ 4) := by
  have kernelSeparation (patch : Fin 4) (source : ℂ) (member : source ∈ motion.domain time index patch) :
      gap / 2 ≤ ‖position - source‖ := by
    have radiusPositive := scales.radius_pos amplitudePositive frequencyPositive ratioPositive (index.val + 1)
    have trapping := evolution.domain_radial_trapping inside index patch (control patch) nonnegative (by linarith) radiusPositive
    have sourceBound : ‖source - patchCentroid motion time index patch‖ < scales.radius (index.val + 1) * (1 + deformation) := by
      simpa only [Metric.mem_ball, dist_eq_norm] using trapping.2 member
    have triangle := norm_add_le (position - source) (source - patchCentroid motion time index patch)
    rw [sub_add_sub_cancel] at triangle
    nlinarith [separated patch]
  rw [evolution.quadrupoleComplexStrain_sum inside index (by positivity : 0 < gap / 2) kernelSeparation]
  have pointIdentity := Section6.circulation_kernelStrain_fourPoint_sum (scales.circulation (index.val + 1))
    (fun patch => patchCentroid motion time index patch) position
  rw [← pointIdentity]
  have mass (patch : Fin 4) : (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) *
      (Real.pi * scales.radius (index.val + 1) ^ 2) = patchSign patch * scales.circulation (index.val + 1) := by
    rw [← scales.patch_circulation amplitudePositive frequencyPositive ratioPositive (index.val + 1)]
    ring
  have pointwiseIdentity (patch : Fin 4) :
      (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) •
        (∫ source in motion.domain time index patch, Section6.biotSavartKernelStrain position source) =
      Section6.vorticityComplexStrain (patchDensity scales motion time index patch) position :=
    (evolution.integral_patchDensity_smul inside index patch _).symm
  simp_rw [pointwiseIdentity]
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  have circulationNonnegative := (scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)).le
  have individual (patch : Fin 4) :
      ‖Section6.vorticityComplexStrain (patchDensity scales motion time index patch) position -
        (Section6.fourPointSign patch * scales.circulation (index.val + 1)) •
          Section6.biotSavartKernelStrain position (patchCentroid motion time index patch)‖ ≤
      1024 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation / (Real.pi * gap ^ 4) := by
    have estimate := evolution.patch_strain_point_error_of_boundaryControl inside amplitudePositive frequencyPositive ratioPositive
      index patch position (control patch) nonnegative small (radiusSmall.trans (separated patch))
    apply estimate.trans
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ gapPositive.le (separated patch) 4) Real.pi_pos.le)
  exact (Finset.sum_le_sum (fun patch _ => individual patch)).trans_eq (by simp only [Fin.sum_univ_succ]; ring)

end EulerNonuniqueness.Paper
