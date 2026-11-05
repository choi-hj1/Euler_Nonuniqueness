import EulerNonuniqueness.Section6.PaperComplexSmoothMoments
import EulerNonuniqueness.Section6.SmoothConjugateInversePower

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000

theorem FinitePatchEvolution.hasDerivAt_patch_fixed_inverse_power_of_boundary_gaps
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
    (center : ℂ) {distance : ℝ} (distancePositive : 0 < distance)
    (separatedNear : ∀ᶠ current in 𝓝 time, ∀ position ∈ motion.domain current index patch, distance ≤ ‖center - position‖)
    (power : ℕ) :
    HasDerivAt (fun current => ∫ position, patchDensity scales motion current index patch position •
        (star (center - position))⁻¹ ^ (power + 1))
      (((power + 1 : ℕ) : ℂ) * ∫ position, patchDensity scales motion time index patch position •
        (star (biotSavart (patchVorticity scales motion time) position) * (star (center - position))⁻¹ ^ (power + 2))) time := by
  let test : ℂ → ℂ := fun position => Section6.smoothConjugateInversePower distance (power + 1) (center - position)
  have smooth : ContDiff ℝ ∞ test :=
    (Section6.smoothConjugateInversePower_contDiff distancePositive _).comp (contDiff_const.sub contDiff_id)
  have actual := evolution.hasDerivAt_patch_complex_smooth_moment_of_boundary_gaps horizonPositive amplitudePositive frequencyPositive ratioPositive
    radiusPositive control separated index patch smooth inside
  have agreement :
      (fun current => ∫ position, patchDensity scales motion current index patch position •
        (star (center - position))⁻¹ ^ (power + 1)) =ᶠ[𝓝 time]
      (fun current => ∫ position, patchDensity scales motion current index patch position • test position) := by
    filter_upwards [separatedNear] with current separation
    apply integral_congr_ae
    apply Eventually.of_forall
    intro position
    by_cases member : position ∈ motion.domain current index patch
    · change patchDensity scales motion current index patch position • _ =
        patchDensity scales motion current index patch position • _
      congr 1
      exact ((Section6.smoothConjugateInversePower_eventuallyEq distancePositive (power + 1)
        (separation position member)).self_of_nhds).symm
    · simp only [patchDensity, indicator_of_not_mem member, zero_smul]
  have result := actual.congr_of_eventuallyEq agreement
  convert result using 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro position
  by_cases member : position ∈ motion.domain time index patch
  · have derivative := (Section6.smoothConjugateInversePower_hasFDerivAt distancePositive power
        (separatedNear.self_of_nhds position member)).comp position
      ((hasFDerivAt_const center position).sub (hasFDerivAt_id position))
    change ((power + 1 : ℕ) : ℂ) * (patchDensity scales motion time index patch position •
      (star (biotSavart (patchVorticity scales motion time) position) * (star (center - position))⁻¹ ^ (power + 2))) =
      patchDensity scales motion time index patch position •
        (fderiv ℝ (Section6.smoothConjugateInversePower distance (power + 1) ∘ HSub.hSub center) position)
          (biotSavart (patchVorticity scales motion time) position)
    rw [derivative.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.zero_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, zero_sub, Complex.conjCLE_apply,
      ContinuousLinearEquiv.coe_coe, map_neg, starRingEnd_apply, star_neg, Complex.real_smul, smul_eq_mul]
    ring
  · simp only [patchDensity, indicator_of_not_mem member, zero_smul, mul_zero]

end EulerNonuniqueness.Paper

