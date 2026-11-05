import EulerNonuniqueness.Section6.PaperMovingSmoothMoment

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.hasDerivAt_patch_moving_smooth_transport_of_boundary_gaps
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
      (∫ position, patchDensity scales motion time index patch position •
        fderiv ℝ test (center time - position)
          (velocity - biotSavart (patchVorticity scales motion time) position)) time := by
  have result := evolution.hasDerivAt_patch_moving_smooth_moment_of_boundary_gaps
    horizonPositive amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index patch
    inside centerDerivative smooth compact
  have atTime : time ∈ Icc 0 horizon := ⟨inside.1.le, inside.2.le⟩
  have derivativeContinuous : Continuous (fun position => fderiv ℝ test (center time - position)) :=
    (smooth.continuous_fderiv (by simp)).comp (continuous_const.sub continuous_id)
  have derivativeIntegrable := evolution.integrable_patchDensity_smul_continuous atTime index patch derivativeContinuous
  have velocityContinuous := (evolution.datum atTime amplitudePositive frequencyPositive ratioPositive).continuous_biotSavart
  have spatialDerivative (position : ℂ) :
      fderiv ℝ (fun other => test (center time - other)) position =
        (fderiv ℝ test (center time - position)).comp (-ContinuousLinearMap.id ℝ ℂ) := by
    have derivative := ((smooth.differentiable (by simp) (center time - position)).hasFDerivAt).comp position
      ((hasFDerivAt_const (center time) position).sub (hasFDerivAt_id position))
    simpa only [zero_sub] using derivative.fderiv
  have spatialSmooth : ContDiff ℝ ∞ (fun position => test (center time - position)) :=
    smooth.comp (contDiff_const.sub contDiff_id)
  have fixedIntegrable := evolution.integrable_patchDensity_smul_continuous atTime index patch
    ((spatialSmooth.continuous_fderiv (by simp)).clm_apply velocityContinuous)
  have movingIntegrable := evolution.integrable_patchDensity_smul_continuous atTime index patch
    (derivativeContinuous.clm_apply continuous_const (g := fun _ => velocity))
  have rateIdentity :
      (∫ position, patchDensity scales motion time index patch position •
        fderiv ℝ (fun other => test (center time - other)) position
          (biotSavart (patchVorticity scales motion time) position)) +
      (∫ position, patchDensity scales motion time index patch position •
        fderiv ℝ test (center time - position)) velocity =
      ∫ position, patchDensity scales motion time index patch position •
        fderiv ℝ test (center time - position)
          (velocity - biotSavart (patchVorticity scales motion time) position) := by
    rw [ContinuousLinearMap.integral_apply derivativeIntegrable velocity]
    have sumIntegral := integral_add fixedIntegrable movingIntegrable
    change _ + (∫ position, patchDensity scales motion time index patch position •
      (fderiv ℝ test (center time - position)) velocity) = _
    rw [← sumIntegral]
    apply integral_congr_ae
    exact Eventually.of_forall fun position => by
      change patchDensity scales motion time index patch position • _ +
        patchDensity scales motion time index patch position • _ = _
      rw [spatialDerivative]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
        ContinuousLinearMap.id_apply, map_neg, map_sub, smul_sub, smul_neg]
      abel
  rw [rateIdentity] at result
  exact result

end EulerNonuniqueness.Paper
