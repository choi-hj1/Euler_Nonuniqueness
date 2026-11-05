import EulerNonuniqueness.Section3.HolderDifferentialAlgebra

open scoped BoundedContinuousFunction

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance quotientDerivativeHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance quotientDerivativeC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph
local instance quotientDerivativeOperatorGroup : SeminormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)

def c1TangentHolderRealCLM : PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf :=
  (ContinuousLinearMap.snd ℝ (ℝ →ᵇ ℂ) PeriodicHolderHalf).comp periodicC1HolderGraph.subtypeL

def extendedContourTangentQuotient (data : PeriodicC1HolderHalf) : PeriodicHolderHalf :=
  holderProduct (holderConjugate data.val.2) (extendedHolderInverse data.val.2)

theorem extendedContourTangentQuotient_eq (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    extendedContourTangentQuotient data = contourTangentQuotient data small := by
  unfold extendedContourTangentQuotient contourTangentQuotient
  rw [extendedHolderInverse_eq data.val.2 (sub_pos.mpr (small.trans_le (min_le_left _ _)))
    (PeriodicC1HolderHalf.tangent_lower_bound data)]

def contourQuotientDerivativeCLM (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf :=
  holderProductRealCLM.precompR PeriodicC1HolderHalf (holderConjugate data.val.2)
    ((holderInverseDerivativeCLM data.val.2).comp c1TangentHolderRealCLM) +
  holderProductRealCLM.precompL PeriodicC1HolderHalf
    (contourHolderConjugateRealCLM.comp c1TangentHolderRealCLM) (extendedHolderInverse data.val.2)

theorem hasFDerivAt_extendedContourTangentQuotient (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    HasFDerivAt extendedContourTangentQuotient (contourQuotientDerivativeCLM data) data := by
  have tangent : HasFDerivAt (fun current : PeriodicC1HolderHalf => current.val.2) c1TangentHolderRealCLM data := by
    exact ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) c1TangentHolderRealCLM
  have inverse_outer : HasFDerivAt extendedHolderInverse (holderInverseDerivativeCLM data.val.2) data.val.2 := by
    exact hasFDerivAt_extendedHolderInverse data.val.2
      (sub_pos.mpr (small.trans_le (min_le_left _ _))) (PeriodicC1HolderHalf.tangent_lower_bound data)
  have inverse : HasFDerivAt (fun current : PeriodicC1HolderHalf => extendedHolderInverse current.val.2)
      ((holderInverseDerivativeCLM data.val.2).comp c1TangentHolderRealCLM) data := by
    have result := HasFDerivAt.comp (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (G := PeriodicHolderHalf)
      (f := fun current : PeriodicC1HolderHalf => current.val.2) (f' := c1TangentHolderRealCLM)
      (g := extendedHolderInverse) (g' := holderInverseDerivativeCLM data.val.2) data inverse_outer tangent
    exact result
  have conjugate : HasFDerivAt (fun current : PeriodicC1HolderHalf => holderConjugate current.val.2)
      (contourHolderConjugateRealCLM.comp c1TangentHolderRealCLM) data := by
    exact contourHolderConjugateRealCLM.hasFDerivAt.comp data tangent
  exact ContinuousLinearMap.hasFDerivAt_of_bilinear (𝕜 := ℝ)
    (E := PeriodicHolderHalf) (F := PeriodicHolderHalf) (G := PeriodicHolderHalf) (G' := PeriodicC1HolderHalf)
    (f := fun current : PeriodicC1HolderHalf => holderConjugate current.val.2)
    (g := fun current : PeriodicC1HolderHalf => extendedHolderInverse current.val.2)
    holderProductRealCLM conjugate inverse

end

end EulerNonuniqueness.Paper
