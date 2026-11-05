import EulerNonuniqueness.Section6.FinitePatchMovingAngularMoment
import EulerNonuniqueness.Section3.FiniteLiteralPatchMotion
import EulerNonuniqueness.Section1.Scales

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

def quadrupolePatchLabels {count : ℕ} (index : Fin count) : Finset (Fin (count * 4)) :=
  Finset.univ.image fun patch : Fin 4 => finProdFinEquiv (index, patch)

theorem quadrupolePatchLabel_injective {count : ℕ} (index : Fin count) :
    Function.Injective (fun patch : Fin 4 => finProdFinEquiv (index, patch)) := by
  intro first second equality
  exact (Prod.mk.inj (finProdFinEquiv.injective equality)).2

namespace FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}

theorem patchCentroid_eq_centroid (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) (patch : Fin 4) :
    patchCentroid flow.patchMotion time index patch = flow.centroid time (finProdFinEquiv (index, patch)) := by
  change (∫ position in flow.domain time (finProdFinEquiv (index, patch)), position) /
    ((volume (flow.domain time (finProdFinEquiv (index, patch)))).toReal : ℂ) = _
  rw [flow.domain_area inside, flow.centroid_eq_complex_integral]
  simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]

theorem quadrupoleDensity_eq_subfamily (flow : FiniteLiteralPatchFlow configuration) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      configuration.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (time : ℝ) (index : Fin count) :
    quadrupoleDensity scales flow.patchMotion time index =
      flow.subfamilyVorticity (quadrupolePatchLabels index) time := by
  funext position
  dsimp only [quadrupoleDensity, subfamilyVorticity, quadrupolePatchLabels]
  rw [Finset.sum_image (fun first _ second _ equality => (quadrupolePatchLabel_injective index) equality)]
  apply Finset.sum_congr rfl
  intro patch _
  change patchDensity scales flow.patchMotion time index patch position =
    (flow.domain time (finProdFinEquiv (index, patch))).indicator
      (fun _ => configuration.density (finProdFinEquiv (index, patch))) position
  rw [densityEquation]
  rfl

theorem integral_quadrupoleDensity_first_moment (flow : FiniteLiteralPatchFlow configuration) (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      configuration.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (radiusEquation : ∀ (index : Fin count) (patch : Fin 4),
      configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1))
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) :
    (∫ position, quadrupoleDensity scales flow.patchMotion time index position • position) =
      (4 * scales.circulation (index.val + 1) : ℝ) • centroidAsymmetry flow.patchMotion time index := by
  rw [flow.quadrupoleDensity_eq_subfamily scales densityEquation,
    flow.integral_subfamilyVorticity_smul (quadrupolePatchLabels index) time (fun position : ℂ => position)
      (fun label _ => flow.domain_identity_integrable time label)]
  dsimp only [quadrupolePatchLabels]
  rw [Finset.sum_image (fun first _ second _ equality => (quadrupolePatchLabel_injective index) equality)]
  have firstMomentIdentity (patch : Fin 4) :
      configuration.density (finProdFinEquiv (index, patch)) •
        (∫ position in flow.domain time (finProdFinEquiv (index, patch)), position) =
      (patchSign patch * scales.circulation (index.val + 1)) •
        patchCentroid flow.patchMotion time index patch := by
    rw [flow.patchCentroid_eq_centroid inside, flow.centroid_eq_complex_integral,
      smul_smul, densityEquation, radiusEquation]
    have circulation := scales.patch_circulation amplitudePositive frequencyPositive ratioPositive (index.val + 1)
    have coefficient : patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4 =
        (patchSign patch * scales.circulation (index.val + 1)) *
          (Real.pi * scales.radius (index.val + 1) ^ 2)⁻¹ := by
      rw [← circulation]
      field_simp [(scales.radius_pos amplitudePositive frequencyPositive ratioPositive (index.val + 1)).ne', Real.pi_ne_zero]
      ring
    rw [coefficient]
  simp_rw [firstMomentIdentity]
  simp only [centroidAsymmetry, Fin.sum_univ_succ, patchSign, Fin.reduceFinMk, Complex.real_smul]
  norm_num
  push_cast
  ring

end FiniteLiteralPatchFlow

end EulerNonuniqueness.Paper
