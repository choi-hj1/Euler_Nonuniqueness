import EulerNonuniqueness.Section3.PaperPassiveSmoothMoments
import EulerNonuniqueness.Section3.PatchStaticMoments
import EulerNonuniqueness.Section6.PaperPatchCentroidAlgebra
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000

private theorem integral_patch_complex_coordinates {count : ℕ} {scales : Scales}
    {motion : PatchMotion count} {time : ℝ} {index : Fin count} {patch : Fin 4} {function : ℂ → ℂ}
    (integrable : Integrable (fun position => patchDensity scales motion time index patch position • function position)) :
    ((∫ position, patchDensity scales motion time index patch position * (function position).re : ℝ) : ℂ) +
      ((∫ position, patchDensity scales motion time index patch position * (function position).im : ℝ) : ℂ) * Complex.I =
        ∫ position, patchDensity scales motion time index patch position • function position := by
  have coordinates := integral_coe_re_add_coe_im integrable
  change (∫ position, ((patchDensity scales motion time index patch position • function position).re : ℂ)) +
      (∫ position, ((patchDensity scales motion time index patch position • function position).im : ℂ)) * Complex.I = _ at coordinates
  simpa only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, add_zero, zero_add, integral_ofReal, integral_complex_ofReal] using coordinates

theorem FinitePatchEvolution.hasDerivAt_patch_complex_first_moment_of_boundary_gaps
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
    (index : Fin count) (patch : Fin 4) (inside : time ∈ Ioo 0 horizon) :
    HasDerivAt (fun current => ∫ position, patchDensity scales motion current index patch position • position)
      (∫ position, patchDensity scales motion time index patch position •
        biotSavart (patchVorticity scales motion time) position) time := by
  have realDerivative := evolution.hasDerivAt_patch_supported_smooth_moment_of_boundary_gaps horizonPositive
    amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index patch Complex.reCLM.contDiff inside
  have imaginaryDerivative := evolution.hasDerivAt_patch_supported_smooth_moment_of_boundary_gaps horizonPositive
    amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index patch Complex.imCLM.contDiff inside
  simp only [ContinuousLinearMap.fderiv] at realDerivative imaginaryDerivative
  have actual := realDerivative.ofReal_comp.add (imaginaryDerivative.ofReal_comp.mul_const Complex.I)
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at actual
  have analytic := evolution.transportAnalyticHypotheses_of_boundary_control amplitudePositive frequencyPositive ratioPositive radiusPositive control
  have fluxIntegrable := evolution.integrable_patchDensity_smul_continuous ⟨inside.1.le, inside.2.le⟩ index patch
    (analytic.continuous_biotSavart ⟨inside.1.le, inside.2.le⟩)
  rw [integral_patch_complex_coordinates fluxIntegrable] at actual
  apply actual.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds inside] with current member
  exact (integral_patch_complex_coordinates
    (evolution.integrable_patchDensity_smul_continuous ⟨member.1.le, member.2.le⟩ index patch continuous_id)).symm

theorem FinitePatchEvolution.patchCentroid_hasDerivAt_of_boundary_gaps
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
    (index : Fin count) (patch : Fin 4) (inside : time ∈ Ioo 0 horizon) :
    HasDerivAt (fun current => patchCentroid motion current index patch)
      (patchAverageVelocity scales motion time index patch (biotSavart (patchVorticity scales motion time))) time := by
  let density := patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4
  let area := Real.pi * scales.radius (index.val + 1) ^ 2
  have patchRadiusPositive := radiusPositive index
  have signNonzero : patchSign patch ≠ 0 := by dsimp only [patchSign]; split_ifs <;> norm_num
  have densityNonzero : density ≠ 0 := mul_ne_zero (mul_ne_zero signNonzero amplitudePositive.ne')
    (pow_ne_zero _ (scales.omega_pos frequencyPositive ratioPositive _).ne')
  have areaPositive : 0 < area := by dsimp only [area]; positivity
  have actual := (evolution.hasDerivAt_patch_complex_first_moment_of_boundary_gaps horizonPositive amplitudePositive frequencyPositive
    ratioPositive radiusPositive control separated index patch inside).const_smul (density * area)⁻¹
  have derivativeIdentity : (density * area)⁻¹ •
      (∫ position, patchDensity scales motion time index patch position • biotSavart (patchVorticity scales motion time) position) =
      patchAverageVelocity scales motion time index patch (biotSavart (patchVorticity scales motion time)) := by
    rw [evolution.integral_patchDensity_smul ⟨inside.1.le, inside.2.le⟩ index patch, smul_smul]
    change ((density * area)⁻¹ * density) • _ = area⁻¹ • _
    congr 1
    field_simp [densityNonzero, areaPositive.ne']
  rw [derivativeIdentity] at actual
  apply actual.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds inside] with current member
  have properties := evolution.2.2.2.1 current ⟨member.1.le, member.2.le⟩ index patch
  have areaIdentity : (volume (motion.domain current index patch)).toReal = area := by
    rw [properties.2.2.1, ENNReal.toReal_ofReal areaPositive.le]
  rw [evolution.integral_patchDensity_smul ⟨member.1.le, member.2.le⟩ index patch, smul_smul]
  unfold patchCentroid
  rw [areaIdentity]
  change (_ / (area : ℂ)) = (((density * area)⁻¹ * density) : ℝ) • _
  rw [Complex.real_smul]
  have coefficient : (density * area)⁻¹ * density = area⁻¹ := by field_simp [densityNonzero, areaPositive.ne']
  rw [coefficient, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]

theorem FinitePatchEvolution.patchCentroid_hasDerivAt_point_field_of_boundary_gaps
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
    (index : Fin count) (patch : Fin 4) (inside : time ∈ Ioo 0 horizon) :
    HasDerivAt (fun current => patchCentroid motion current index patch)
      (Section6.fourPointField (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
          (fun source => patchCentroid motion time index source) patch +
        biotSavart (externalPatchVorticity scales motion time index) (patchCentroid motion time index patch) +
        quadrupoleInternalPatchResidual scales motion time index patch + quadrupoleExternalReceiverResidual scales motion time index patch) time := by
  have actual := evolution.patchCentroid_hasDerivAt_of_boundary_gaps horizonPositive amplitudePositive frequencyPositive ratioPositive
    radiusPositive control separated index patch inside
  rw [evolution.patch_average_velocity_decomposition ⟨inside.1.le, inside.2.le⟩ index patch] at actual
  exact actual

end EulerNonuniqueness.Paper
