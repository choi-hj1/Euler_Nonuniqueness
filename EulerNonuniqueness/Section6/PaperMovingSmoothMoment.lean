import EulerNonuniqueness.Section6.PaperComplexSmoothMoments
import EulerNonuniqueness.General.MovingL1MomentDerivative
import EulerNonuniqueness.General.TranslatedIntegralDerivative
import EulerNonuniqueness.General.CompactSmoothLipschitz

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff ENNReal

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.hasDerivAt_patch_moving_smooth_moment_of_boundary_gaps
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (horizonPositive : 0 < horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (radiusPositive : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
    (control : ∀ current ∈ Icc 0 horizon, ∀ index patch,
      ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle scales motion current index patch bound)
    (separated : ∀ current ∈ Icc 0 horizon, ∀ (index other : Fin count) (patch otherPatch : Fin 4),
      (other, otherPatch) ≠ (index, patch) →
      8 * scales.radius (index.val + 1) + 8 * scales.radius (other.val + 1) <
        dist (motion.boundary current index patch 0) (motion.boundary current other otherPatch 0))
    (index : Fin count) (patch : Fin 4) (inside : time ∈ Ioo 0 horizon)
    {center : ℝ → ℂ} {velocity : ℂ} (centerDerivative : HasDerivAt center velocity time)
    {test : ℂ → ℂ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    HasDerivAt (fun current => ∫ position, patchDensity scales motion current index patch position •
        test (center current - position))
      ((∫ position, patchDensity scales motion time index patch position •
        fderiv ℝ (fun other => test (center time - other)) position
          (biotSavart (patchVorticity scales motion time) position)) +
       (∫ position, patchDensity scales motion time index patch position •
        fderiv ℝ test (center time - position)) velocity) time := by
  have atTime : time ∈ Icc 0 horizon := ⟨inside.1.le, inside.2.le⟩
  have near := Icc_mem_nhds inside.1 inside.2
  have densityIntegrable (current : ℝ) (member : current ∈ Icc 0 horizon) :
      Integrable (patchDensity scales motion current index patch) := by
    have properties := evolution.2.2.2.1 current member index patch
    exact patchDensity_integrable scales motion current index patch properties.1 properties.2.1
  have strong := evolution.tendsto_eLpNorm_patch_sub_of_boundary_gaps atTime radiusPositive control index patch
    (fun other otherPatch different => separated time atTime index other patch otherPatch different)
  rw [nhdsWithin_eq_nhds.mpr near] at strong
  obtain ⟨testConstant, lipschitz⟩ := General.exists_lipschitzWith_of_contDiff_compactSupport
    (smooth.of_le (by simp)) compact
  obtain ⟨centerConstant, centerPositive, centerBound⟩ := centerDerivative.hasFDerivAt.isBigO_sub.exists_pos
  have spatialSmooth : ContDiff ℝ ∞ (fun position => test (center time - position)) :=
    smooth.comp (contDiff_const.sub contDiff_id)
  have fixedDerivative := evolution.hasDerivAt_patch_complex_smooth_moment_of_boundary_gaps
    horizonPositive amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index patch
    spatialSmooth inside
  have movingDerivative := (General.hasFDerivAt_integral_translate_of_lipschitz
    (test := test) (densityIntegrable time atTime) (smooth.of_le (by simp)) lipschitz (center time)
    (evolution.integrable_patchDensity_smul_continuous atTime index patch
      (smooth.continuous.comp (continuous_const.sub continuous_id)))).comp_hasDerivAt time centerDerivative
  have nearIntegrable : ∀ᶠ current in 𝓝 time,
      Integrable (patchDensity scales motion current index patch) := by
    filter_upwards [near] with current member
    exact densityIntegrable current member
  apply General.hasDerivAt_moving_L1_moment
    (density := fun current => patchDensity scales motion current index patch)
    (kernel := fun current position => test (center current - position))
    (constant := (testConstant : ℝ) * centerConstant)
    nearIntegrable strong _ _ _ fixedDerivative movingDerivative
  · exact Eventually.of_forall fun current =>
      ((smooth.continuous.comp (continuous_const.sub continuous_id)).sub
        (smooth.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · filter_upwards [centerBound.bound] with current bound
    apply Eventually.of_forall
    intro position _
    have first := lipschitz.norm_sub_le (center current - position) (center time - position)
    have difference : (center current - position) - (center time - position) = center current - center time := by abel
    rw [difference] at first
    have second := mul_le_mul_of_nonneg_left bound testConstant.coe_nonneg
    simpa only [Real.norm_eq_abs, mul_assoc] using first.trans second
  · filter_upwards [near] with current member
    exact ⟨evolution.integrable_patchDensity_smul_continuous member index patch
        (smooth.continuous.comp (continuous_const.sub continuous_id)),
      evolution.integrable_patchDensity_smul_continuous member index patch
        (smooth.continuous.comp (continuous_const.sub continuous_id)),
      evolution.integrable_patchDensity_smul_continuous atTime index patch
        (smooth.continuous.comp (continuous_const.sub continuous_id)),
      evolution.integrable_patchDensity_smul_continuous atTime index patch
        (smooth.continuous.comp (continuous_const.sub continuous_id))⟩

end EulerNonuniqueness.Paper
