import EulerNonuniqueness.Section3.PeriodicHilbertC1
import EulerNonuniqueness.Section3.ComplexHolderBanach

open MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

local instance : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance : Module ℂ PeriodicHolderHalf := Submodule.module complexPeriodicHolderGraph
local instance : Module ℂ PeriodicC1HolderHalf := Submodule.module complexPeriodicC1HolderGraph
local instance : NormedSpace ℂ PeriodicHolderHalf := complexHolderNormedSpace
local instance : NormedSpace ℂ PeriodicC1HolderHalf := complexC1HolderNormedSpace

theorem circleCauchyCLM_smul_complex (scalar : ℂ) (density : PeriodicHolderHalf) :
    circleCauchyCLM (scalar • density) = scalar • circleCauchyCLM density := by
  apply PeriodicHolderHalf.ext_value
  intro target
  rw [circleCauchyCLM_translated]
  change _ = scalar * (circleCauchyCLM density).val.1 target
  rw [circleCauchyCLM_translated]
  have integrand : circleCauchyTranslatedRemainder (scalar • density).val.1 target =
      fun source => scalar * circleCauchyTranslatedRemainder density.val.1 target source := by
    funext source
    unfold circleCauchyTranslatedRemainder
    simp only [complexHolder_smul_value]
    ring
  rw [integrand, intervalIntegral.integral_const_mul, complexHolder_smul_value]
  ring

theorem holderConjugate_smul_complex (scalar : ℂ) (density : PeriodicHolderHalf) :
    holderConjugate (scalar • density) = star scalar • holderConjugate density := by
  apply PeriodicHolderHalf.ext_value
  intro target
  change star (scalar * density.val.1 target) = star scalar * star (density.val.1 target)
  simpa only [mul_comm] using star_mul scalar (density.val.1 target)

theorem periodicHilbertCLM_smul_complex (scalar : ℂ) (density : PeriodicHolderHalf) :
    periodicHilbertCLM (scalar • density) = scalar • periodicHilbertCLM density := by
  have first := circleCauchyCLM_smul_complex scalar density
  have second := circleCauchyCLM_smul_complex (star scalar) (holderConjugate density)
  rw [← holderConjugate_smul_complex] at second
  apply PeriodicHolderHalf.ext_value
  intro target
  change (1 / (2 * Real.pi)) •
    ((circleCauchyCLM (scalar • density)).val.1 target +
      star ((circleCauchyCLM (holderConjugate (scalar • density))).val.1 target)) =
    scalar * ((1 / (2 * Real.pi)) •
      ((circleCauchyCLM density).val.1 target +
        star ((circleCauchyCLM (holderConjugate density)).val.1 target)))
  rw [first, second]
  simp only [complexHolder_smul_value, star_mul, star_star, Complex.real_smul]
  ring

def periodicHilbertCCLM : PeriodicHolderHalf →L[ℂ] PeriodicHolderHalf :=
  LinearMap.mkContinuous (𝕜 := ℂ) (𝕜₂ := ℂ) (E := PeriodicHolderHalf) (F := PeriodicHolderHalf)
    { toFun := periodicHilbertCLM
      map_add' := periodicHilbertCLM.map_add
      map_smul' := periodicHilbertCLM_smul_complex }
    periodicHilbertBound periodicHilbertCLM_norm_bound

theorem periodicHilbertC1_smul_complex (scalar : ℂ) (data : PeriodicC1HolderHalf) :
    periodicHilbertC1 (scalar • data) = scalar • periodicHilbertC1 data := by
  have embedding : c1ValueHolder (scalar • data) = scalar • c1ValueHolder data := by
    apply PeriodicHolderHalf.ext_value
    intro label
    rfl
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (periodicHilbertCLM (c1ValueHolder (scalar • data))).val.1 label = _
  rw [embedding, periodicHilbertCLM_smul_complex]
  rfl

def periodicHilbertC1CCLM : PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf :=
  LinearMap.mkContinuous (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
    { toFun := periodicHilbertC1
      map_add' := periodicHilbertC1_add
      map_smul' := periodicHilbertC1_smul_complex }
    (2 * periodicHilbertBound) periodicHilbertC1_norm_bound

end

end EulerNonuniqueness.Paper
