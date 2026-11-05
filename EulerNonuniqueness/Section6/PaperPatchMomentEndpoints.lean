import EulerNonuniqueness.Section3.PaperPassiveSmoothMoments
import EulerNonuniqueness.Section8.SupportedPassiveMomentEndpoints

noncomputable section

open Set MeasureTheory Filter Function
open scoped Topology ContDiff

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.patch_supported_smooth_moment_closed_derivative_of_boundary_gaps
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon : ℝ}
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
    (index : Fin count) (patch : Fin 4) {test : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ test) :
    ContinuousOn (fun current => ∫ position, patchDensity scales motion current index patch position * test position) (Icc 0 horizon) ∧
    ContinuousOn (fun current => ∫ position, patchDensity scales motion current index patch position *
      fderiv ℝ test position (biotSavart (patchVorticity scales motion current) position)) (Icc 0 horizon) ∧
    ∀ time ∈ Icc 0 horizon,
      HasDerivWithinAt (fun current => ∫ position, patchDensity scales motion current index patch position * test position)
        (∫ position, patchDensity scales motion time index patch position *
          fderiv ℝ test position (biotSavart (patchVorticity scales motion time) position)) (Icc 0 horizon) time := by
  have analytic := evolution.transportAnalyticHypotheses_of_boundary_control
    amplitudePositive frequencyPositive ratioPositive radiusPositive control
  have densityContinuous : ContinuousInLpOn horizon 2 (fun current => patchDensity scales motion current index patch) := by
    simpa only [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num] using
      evolution.continuousInLp_patch_of_boundary_gaps radiusPositive control separated index patch (exponent := 2) (by norm_num)
  obtain ⟨radius, positiveRadius, domains⟩ := evolution.exists_uniform_domain_support_of_boundary_control radiusPositive control
  apply (evolution.2.1 index patch).supported_passive_smooth_moment_closed_derivative densityContinuous
    analytic.continuousInLp_biotSavart horizonPositive positiveRadius.le ?_ smooth
  intro current member position nonzero
  apply domains current member index patch
  by_contra outside
  exact nonzero (Set.indicator_of_not_mem outside _)

end EulerNonuniqueness.Paper

