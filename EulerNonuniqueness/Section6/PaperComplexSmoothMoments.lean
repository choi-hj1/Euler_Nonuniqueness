import EulerNonuniqueness.Section6.PaperCentroidMomentDynamics
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

theorem FinitePatchEvolution.hasDerivAt_patch_complex_smooth_moment_of_boundary_gaps
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
    (index : Fin count) (patch : Fin 4) {test : ℂ → ℂ} (smooth : ContDiff ℝ ∞ test) (inside : time ∈ Ioo 0 horizon) :
    HasDerivAt (fun current => ∫ position, patchDensity scales motion current index patch position • test position)
      (∫ position, patchDensity scales motion time index patch position •
        fderiv ℝ test position (biotSavart (patchVorticity scales motion time) position)) time := by
  have reDifferential (position : ℂ) :
      fderiv ℝ (fun other => (test other).re) position = Complex.reCLM.comp (fderiv ℝ test position) :=
    (Complex.reCLM.hasFDerivAt.comp position ((smooth.differentiable (by simp) position).hasFDerivAt)).fderiv
  have imDifferential (position : ℂ) :
      fderiv ℝ (fun other => (test other).im) position = Complex.imCLM.comp (fderiv ℝ test position) :=
    (Complex.imCLM.hasFDerivAt.comp position ((smooth.differentiable (by simp) position).hasFDerivAt)).fderiv
  have realDerivative := evolution.hasDerivAt_patch_supported_smooth_moment_of_boundary_gaps horizonPositive
    amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index patch (Complex.reCLM.contDiff.comp smooth) inside
  have imaginaryDerivative := evolution.hasDerivAt_patch_supported_smooth_moment_of_boundary_gaps horizonPositive
    amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index patch (Complex.imCLM.contDiff.comp smooth) inside
  change HasDerivAt (fun current => ∫ position, patchDensity scales motion current index patch position * (test position).re)
    (∫ position, patchDensity scales motion time index patch position *
      fderiv ℝ (fun other => (test other).re) position (biotSavart (patchVorticity scales motion time) position)) time at realDerivative
  change HasDerivAt (fun current => ∫ position, patchDensity scales motion current index patch position * (test position).im)
    (∫ position, patchDensity scales motion time index patch position *
      fderiv ℝ (fun other => (test other).im) position (biotSavart (patchVorticity scales motion time) position)) time at imaginaryDerivative
  simp only [reDifferential, ContinuousLinearMap.comp_apply, Complex.reCLM_apply] at realDerivative
  simp only [imDifferential, ContinuousLinearMap.comp_apply, Complex.imCLM_apply] at imaginaryDerivative
  have actual := realDerivative.ofReal_comp.add (imaginaryDerivative.ofReal_comp.mul_const Complex.I)
  have analytic := evolution.transportAnalyticHypotheses_of_boundary_control amplitudePositive frequencyPositive ratioPositive radiusPositive control
  have fluxContinuous := (smooth.continuous_fderiv (by simp)).clm_apply
    (analytic.continuous_biotSavart ⟨inside.1.le, inside.2.le⟩)
  have fluxIntegrable := evolution.integrable_patchDensity_smul_continuous ⟨inside.1.le, inside.2.le⟩ index patch fluxContinuous
  rw [integral_patch_complex_coordinates fluxIntegrable] at actual
  apply actual.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds inside] with current member
  exact (integral_patch_complex_coordinates
    (evolution.integrable_patchDensity_smul_continuous ⟨member.1.le, member.2.le⟩ index patch smooth.continuous)).symm

end EulerNonuniqueness.Paper

