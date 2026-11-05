import EulerNonuniqueness.Section6.PaperQuadrupoleStrainDerivative
import EulerNonuniqueness.Section3.FiniteMovingPatchMotion
import EulerNonuniqueness.Section8.MeasurableKernelConvolution

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Section6

theorem measurable_vorticityComplexStrain_of_measurable_vorticity
    {parameter : Type*} [MeasurableSpace parameter] {vorticity : parameter → Vorticity}
    (sourceMeasurable : Measurable (Function.uncurry vorticity)) :
    Measurable (fun point : parameter × ℂ => vorticityComplexStrain (vorticity point.1) point.2) := by
  have kernel : Measurable (fun position : ℂ => -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) / star position ^ 2) := by
    fun_prop
  exact measurable_kernel_convolution sourceMeasurable kernel

theorem measurable_vorticityComplexStrain_along
    {parameter : Type*} [MeasurableSpace parameter] {vorticity : parameter → Vorticity}
    (sourceMeasurable : Measurable (Function.uncurry vorticity))
    {location : parameter → ℂ} (locationMeasurable : Measurable location) :
    Measurable (fun time => vorticityComplexStrain (vorticity time) (location time)) :=
  (measurable_vorticityComplexStrain_of_measurable_vorticity sourceMeasurable).comp
    (measurable_id.prodMk locationMeasurable)

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

variable {count : ℕ}

theorem measurable_quadrupoleDensity (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (index : Fin count) :
    Measurable (fun point : ℝ × ℂ => quadrupoleDensity scales family.patchMotion point.1 index point.2) := by
  change Measurable (fun point : ℝ × ℂ => ∑ patch : Fin 4,
    patchDensity scales family.patchMotion point.1 index patch point.2)
  apply Finset.measurable_sum
  intro patch _
  have identity : (fun point : ℝ × ℂ => patchDensity scales family.patchMotion point.1 index patch point.2) =
      fun point => family.patchVorticity point.1 (finProdFinEquiv (index, patch)) point.2 := by
    funext point
    exact congrFun (family.patchDensity_eq scales densityEquation point.1 index patch) point.2
  rw [identity]
  exact family.measurable_patchVorticity _

theorem measurable_quadrupole_strain_along (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (index : Fin count) {location : ℝ → ℂ} (locationMeasurable : Measurable location) :
    Measurable (fun time => Section6.vorticityComplexStrain
      (quadrupoleDensity scales family.patchMotion time index) (location time)) := by
  have source : Measurable (Function.uncurry
      (fun time => quadrupoleDensity scales family.patchMotion time index)) :=
    family.measurable_quadrupoleDensity scales densityEquation index
  exact Section6.measurable_vorticityComplexStrain_along source locationMeasurable

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
