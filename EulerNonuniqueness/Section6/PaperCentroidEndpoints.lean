import EulerNonuniqueness.Section6.PaperCentroidMomentDynamics
import EulerNonuniqueness.Section6.PaperPatchMomentEndpoints
import EulerNonuniqueness.General.ODEClosedIntervalDerivative

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000

theorem FinitePatchEvolution.patchCentroid_closed_derivative_of_boundary_gaps
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
    (index : Fin count) (patch : Fin 4) :
    ContinuousOn (fun current => patchCentroid motion current index patch) (Icc 0 horizon) ∧
    ContinuousOn (fun current => patchAverageVelocity scales motion current index patch
      (biotSavart (patchVorticity scales motion current))) (Icc 0 horizon) ∧
    ∀ time ∈ Icc 0 horizon, HasDerivWithinAt (fun current => patchCentroid motion current index patch)
      (patchAverageVelocity scales motion time index patch (biotSavart (patchVorticity scales motion time))) (Icc 0 horizon) time := by
  have realData := evolution.patch_supported_smooth_moment_closed_derivative_of_boundary_gaps horizonPositive
    amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index patch Complex.reCLM.contDiff
  have imaginaryData := evolution.patch_supported_smooth_moment_closed_derivative_of_boundary_gaps horizonPositive
    amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index patch Complex.imCLM.contDiff
  simp only [ContinuousLinearMap.fderiv, Complex.reCLM_apply, Complex.imCLM_apply] at realData imaginaryData
  let density := patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4
  let area := Real.pi * scales.radius (index.val + 1) ^ 2
  let coefficient := (density * area)⁻¹
  have patchRadiusPositive := radiusPositive index
  have signNonzero : patchSign patch ≠ 0 := by dsimp only [patchSign]; split_ifs <;> norm_num
  have densityNonzero : density ≠ 0 := mul_ne_zero (mul_ne_zero signNonzero amplitudePositive.ne')
    (pow_ne_zero _ (scales.omega_pos frequencyPositive ratioPositive _).ne')
  have areaPositive : 0 < area := by dsimp only [area]; positivity
  have normalization : coefficient * density = area⁻¹ := by
    dsimp only [coefficient]
    field_simp [densityNonzero, areaPositive.ne']
  have normalizedIntegral (current : ℝ) (member : current ∈ Icc 0 horizon) (function : ℂ → ℂ) :
      coefficient • (∫ position, patchDensity scales motion current index patch position • function position) =
        area⁻¹ • ∫ position in motion.domain current index patch, function position := by
    rw [evolution.integral_patchDensity_smul member index patch, smul_smul]
    change (coefficient * density) • _ = area⁻¹ • _
    rw [normalization]
  have centroidIdentity (current : ℝ) (member : current ∈ Icc 0 horizon) :
      patchCentroid motion current index patch = coefficient •
        (∫ position, patchDensity scales motion current index patch position • position) := by
    have properties := evolution.2.2.2.1 current member index patch
    have areaIdentity : (volume (motion.domain current index patch)).toReal = area := by
      rw [properties.2.2.1, ENNReal.toReal_ofReal areaPositive.le]
    rw [normalizedIntegral current member]
    unfold patchCentroid
    rw [areaIdentity, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]
  have coordinates (current : ℝ) {function : ℂ → ℂ}
      (integrable : Integrable (fun position => patchDensity scales motion current index patch position • function position)) :
      ((∫ position, patchDensity scales motion current index patch position * (function position).re : ℝ) : ℂ) +
        ((∫ position, patchDensity scales motion current index patch position * (function position).im : ℝ) : ℂ) * Complex.I =
          ∫ position, patchDensity scales motion current index patch position • function position := by
    have actual := integral_coe_re_add_coe_im integrable
    change (∫ position, ((patchDensity scales motion current index patch position • function position).re : ℂ)) +
      (∫ position, ((patchDensity scales motion current index patch position • function position).im : ℂ)) * Complex.I = _ at actual
    simpa only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, add_zero, zero_add, integral_complex_ofReal] using actual
  have analytic := evolution.transportAnalyticHypotheses_of_boundary_control amplitudePositive frequencyPositive ratioPositive radiusPositive control
  have momentContinuous : ContinuousOn (fun current => ∫ position, patchDensity scales motion current index patch position • position) (Icc 0 horizon) := by
    apply ((Complex.continuous_ofReal.comp_continuousOn realData.1).add
      ((Complex.continuous_ofReal.comp_continuousOn imaginaryData.1).mul continuousOn_const)).congr
    intro current member
    exact (coordinates current (evolution.integrable_patchDensity_smul_continuous member index patch continuous_id)).symm
  have fluxContinuous : ContinuousOn (fun current => ∫ position, patchDensity scales motion current index patch position •
      biotSavart (patchVorticity scales motion current) position) (Icc 0 horizon) := by
    apply ((Complex.continuous_ofReal.comp_continuousOn realData.2.1).add
      ((Complex.continuous_ofReal.comp_continuousOn imaginaryData.2.1).mul continuousOn_const)).congr
    intro current member
    exact (coordinates current (evolution.integrable_patchDensity_smul_continuous member index patch
      (analytic.continuous_biotSavart member))).symm
  have centroidContinuous : ContinuousOn (fun current => patchCentroid motion current index patch) (Icc 0 horizon) :=
    (momentContinuous.const_smul coefficient).congr centroidIdentity
  have velocityContinuous : ContinuousOn (fun current => patchAverageVelocity scales motion current index patch
      (biotSavart (patchVorticity scales motion current))) (Icc 0 horizon) := by
    apply (fluxContinuous.const_smul coefficient).congr
    intro current member
    exact (normalizedIntegral current member _).symm
  let velocity := fun current => patchAverageVelocity scales motion current index patch (biotSavart (patchVorticity scales motion current))
  let extension := fun current => velocity (projIcc 0 horizon horizonPositive.le current)
  have extensionContinuous : Continuous extension :=
    (continuousOn_iff_continuous_restrict.mp velocityContinuous).comp continuous_projIcc
  have agreement (current : ℝ) (member : current ∈ Icc 0 horizon) : extension current = velocity current := by
    simp only [extension, projIcc_of_mem horizonPositive.le member]
  have interiorEquation (current : ℝ) (member : current ∈ Ioo 0 horizon) :
      HasDerivAt (fun other => patchCentroid motion other index patch) (extension current) current := by
    rw [agreement current ⟨member.1.le, member.2.le⟩]
    exact evolution.patchCentroid_hasDerivAt_of_boundary_gaps horizonPositive amplitudePositive frequencyPositive ratioPositive
      radiusPositive control separated index patch member
  refine ⟨centroidContinuous, velocityContinuous, ?_⟩
  intro time member
  have actual := hasDerivWithinAt_Icc_of_continuous_interior_derivative centroidContinuous extensionContinuous interiorEquation time member
  rwa [agreement time member] at actual

end EulerNonuniqueness.Paper
