import EulerNonuniqueness.Section3.ContourAntiholomorphicFunctional
import EulerNonuniqueness.Section3.ContourAnalyticMoments

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 2000000

local instance antiholomorphicPairC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph
local instance antiholomorphicPairC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph
local instance antiholomorphicPairOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := ℂ) (σ₁₂ := RingHom.id ℝ)
local instance antiholomorphicPairOperatorSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := ℂ) (σ₁₂ := RingHom.id ℝ)

def contourAntiholomorphicPairCLM : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] ℂ :=
  let tangent := contourTangentFunctionCLM.comp c1ConjugateCLM
  let product : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] (ℝ →ᵇ ℂ) :=
    ((ContinuousLinearMap.precompR PeriodicC1HolderHalf
    (ContinuousLinearMap.mul ℝ (ℝ →ᵇ ℂ))).flip tangent).comp contourValueFunctionCLM
  let integral := ((ContinuousLinearMap.mul ℝ ℂ) (Complex.I / 2)).comp
    (boundedIntervalIntegral (-Real.pi) Real.pi)
  ((ContinuousLinearMap.compL ℝ PeriodicC1HolderHalf (ℝ →ᵇ ℂ) ℂ) integral).comp product

theorem contourAntiholomorphicPairCLM_apply (first second : PeriodicC1HolderHalf) :
    contourAntiholomorphicPairCLM first second = (Complex.I / 2) *
      ∫ label in (-Real.pi)..Real.pi, first.val.1 label * star (second.val.2.val.1 label) := rfl

theorem contourAntiholomorphicPairCLM_norm_bound (first second : PeriodicC1HolderHalf) :
    ‖contourAntiholomorphicPairCLM first second‖ ≤
      ‖contourAntiholomorphicPairCLM‖ * ‖first‖ * ‖second‖ :=
  ((contourAntiholomorphicPairCLM first).le_opNorm second).trans
    (mul_le_mul_of_nonneg_right (contourAntiholomorphicPairCLM.le_opNorm first) (norm_nonneg second))

theorem contourAntiholomorphicFunctional_eq_pair (kernel : ℂ → ℂ)
    (data kernelData : PeriodicC1HolderHalf)
    (values : ∀ label, kernelData.val.1 label = kernel (data.val.1 label)) :
    contourAntiholomorphicFunctional kernel data =
      contourAntiholomorphicPairCLM (c1Product data kernelData) data := by
  rw [contourAntiholomorphicPairCLM_apply]
  unfold contourAntiholomorphicFunctional
  congr 1
  apply intervalIntegral.integral_congr
  intro label _
  change data.val.1 label * kernel (data.val.1 label) * star (data.val.2.val.1 label) =
    (data.val.1 label * kernelData.val.1 label) * star (data.val.2.val.1 label)
  rw [values]

end EulerNonuniqueness.Paper
