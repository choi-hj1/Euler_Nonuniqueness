import EulerNonuniqueness.Section6.PaperComplexSmoothMoments
import EulerNonuniqueness.General.StrongL1MovingPairing

noncomputable section

open Set MeasureTheory Function
open scoped Topology ENNReal

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.continuousOn_patch_moving_compact_moment_of_boundary_gaps
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon)
    (radiusPositive : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
    (control : ∀ current ∈ Icc 0 horizon, ∀ index patch,
      ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle scales motion current index patch bound)
    (separated : ∀ current ∈ Icc 0 horizon, ∀ (index other : Fin count) (patch otherPatch : Fin 4),
      (other, otherPatch) ≠ (index, patch) →
      8 * scales.radius (index.val + 1) + 8 * scales.radius (other.val + 1) <
        dist (motion.boundary current index patch 0) (motion.boundary current other otherPatch 0))
    (index : Fin count) (patch : Fin 4) {center : ℝ → ℂ}
    (centerContinuous : ContinuousOn center (Icc 0 horizon))
    {test : ℂ → ℂ} (testContinuous : Continuous test) (compact : HasCompactSupport test) :
    ContinuousOn (fun current => ∫ position, patchDensity scales motion current index patch position •
      test (center current - position)) (Icc 0 horizon) := by
  have densityContinuous := evolution.continuousInLp_patch_of_boundary_gaps radiusPositive control separated
    index patch (exponent := 1) (by norm_num)
  simp only [ENNReal.ofReal_one] at densityContinuous
  obtain ⟨exponentBound, membership, continuous⟩ := densityContinuous
  letI : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨exponentBound⟩
  have centerRestricted : Continuous (fun current : Icc 0 horizon => center current) :=
    continuousOn_iff_continuous_restrict.mp centerContinuous
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuousOn testContinuous.continuousOn
  have testBound (position : ℂ) : ‖test position‖ ≤ max bound 0 := by
    by_cases member : position ∈ tsupport test
    · exact (bounded position member).trans (le_max_left _ _)
    · have zero : test position = 0 := by
        by_contra nonzero
        exact member (subset_closure nonzero)
      rw [zero, norm_zero]
      exact le_max_right _ _
  have realContinuous : Continuous (fun current : Icc 0 horizon => ∫ position,
      patchDensity scales motion current index patch position * (test (center current - position)).re) := by
    apply continuous_integral_mul_of_continuous_L1 membership continuous
    · intro current
      exact (Complex.continuous_re.comp (testContinuous.comp (continuous_const.sub continuous_id))).measurable
    · intro position
      exact Complex.continuous_re.comp (testContinuous.comp (centerRestricted.sub continuous_const))
    · intro current position
      exact (Complex.abs_re_le_norm _).trans (testBound _)
  have imaginaryContinuous : Continuous (fun current : Icc 0 horizon => ∫ position,
      patchDensity scales motion current index patch position * (test (center current - position)).im) := by
    apply continuous_integral_mul_of_continuous_L1 membership continuous
    · intro current
      exact (Complex.continuous_im.comp (testContinuous.comp (continuous_const.sub continuous_id))).measurable
    · intro position
      exact Complex.continuous_im.comp (testContinuous.comp (centerRestricted.sub continuous_const))
    · intro current position
      exact (Complex.abs_im_le_norm _).trans (testBound _)
  have combined := (Complex.continuous_ofReal.comp realContinuous).add
    ((Complex.continuous_ofReal.comp imaginaryContinuous).mul continuous_const (g := fun _ => Complex.I))
  apply continuousOn_iff_continuous_restrict.mpr
  apply combined.congr
  intro current
  have kernelContinuous : Continuous (fun position => test (center current - position)) :=
    testContinuous.comp (continuous_const.sub continuous_id)
  have integrable := evolution.integrable_patchDensity_smul_continuous current.property index patch
    kernelContinuous
  have coordinates := integral_coe_re_add_coe_im integrable
  change (∫ position, ((patchDensity scales motion current index patch position •
    test (center current - position)).re : ℂ)) +
    (∫ position, ((patchDensity scales motion current index patch position •
      test (center current - position)).im : ℂ)) * Complex.I = _ at coordinates
  simpa only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, zero_add, integral_ofReal,
    integral_complex_ofReal] using coordinates

end EulerNonuniqueness.Paper
