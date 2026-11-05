import EulerNonuniqueness.Section3.ContourQuotientDerivative

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance tangentVelocityHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance tangentVelocityC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

def holderContourVelocityTangent (data : PeriodicC1HolderHalf) : PeriodicHolderHalf :=
  -(1 / (4 * Real.pi) : ℂ) • holderProduct (holderConjugate data.val.2)
    (holderConjugate (extendedContourCauchy data (extendedContourTangentQuotient data) +
      ((Real.pi : ℂ) * Complex.I) • extendedContourTangentQuotient data))

theorem holderContourVelocityTangent_eq (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    holderContourVelocityTangent data = contourVelocityDerivativeHolder data small := by
  unfold holderContourVelocityTangent contourVelocityDerivativeHolder
  rw [extendedContourTangentQuotient_eq data small, extendedContourCauchy_eq _ _ small]
  have scalar_identity : -(1 / (4 * Real.pi) : ℂ) = -((1 / (4 * Real.pi) : ℝ) : ℂ) := by push_cast; rfl
  rw [scalar_identity]
  apply PeriodicHolderHalf.ext_value
  intro label
  rfl

theorem differentiableAt_holderContourVelocityTangent (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    DifferentiableAt ℝ holderContourVelocityTangent data := by
  obtain ⟨radius, near, radius_small⟩ := exists_between small
  have quotient : DifferentiableAt ℝ extendedContourTangentQuotient data :=
    HasFDerivAt.differentiableAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf)
      (hasFDerivAt_extendedContourTangentQuotient data small)
  have pair : DifferentiableAt ℝ
      (fun current : PeriodicC1HolderHalf => (current, extendedContourTangentQuotient current)) data := by
    exact DifferentiableAt.prodMk (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
      (F := PeriodicC1HolderHalf) (G := PeriodicHolderHalf) differentiableAt_id quotient
  have outer : DifferentiableAt ℝ
      (fun pair : PeriodicC1HolderHalf × PeriodicHolderHalf => extendedContourCauchy pair.1 pair.2)
      (data, extendedContourTangentQuotient data) :=
    HasFDerivAt.differentiableAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf × PeriodicHolderHalf) (F := PeriodicHolderHalf)
      (hasFDerivAt_contourCauchy_joint data (extendedContourTangentQuotient data) near radius_small)
  have cauchy : DifferentiableAt ℝ
      (fun current : PeriodicC1HolderHalf => extendedContourCauchy current (extendedContourTangentQuotient current)) data := by
    exact DifferentiableAt.comp (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
      (F := PeriodicC1HolderHalf × PeriodicHolderHalf) (G := PeriodicHolderHalf)
      (f := fun current : PeriodicC1HolderHalf => (current, extendedContourTangentQuotient current)) data outer pair
  have scaled : DifferentiableAt ℝ
      (fun current : PeriodicC1HolderHalf => ((Real.pi : ℂ) * Complex.I) • extendedContourTangentQuotient current) data := by
    exact DifferentiableAt.const_smul (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf)
      (R := ℂ) quotient ((Real.pi : ℂ) * Complex.I)
  have sum : DifferentiableAt ℝ
      (fun current : PeriodicC1HolderHalf => extendedContourCauchy current (extendedContourTangentQuotient current) +
        ((Real.pi : ℂ) * Complex.I) • extendedContourTangentQuotient current) data := by
    exact DifferentiableAt.add (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) cauchy scaled
  have conjugated : DifferentiableAt ℝ
      (fun current : PeriodicC1HolderHalf => holderConjugate
        (extendedContourCauchy current (extendedContourTangentQuotient current) +
          ((Real.pi : ℂ) * Complex.I) • extendedContourTangentQuotient current)) data := by
    exact contourHolderConjugateRealCLM.differentiableAt.comp data sum
  have tangent : DifferentiableAt ℝ (fun current : PeriodicC1HolderHalf => holderConjugate current.val.2) data := by
    exact ContinuousLinearMap.differentiableAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf)
      (contourHolderConjugateRealCLM.comp c1TangentHolderRealCLM)
  have product : DifferentiableAt ℝ
      (fun current : PeriodicC1HolderHalf => holderProduct (holderConjugate current.val.2)
        (holderConjugate (extendedContourCauchy current (extendedContourTangentQuotient current) +
          ((Real.pi : ℂ) * Complex.I) • extendedContourTangentQuotient current))) data := by
    have derivative := ContinuousLinearMap.hasFDerivAt_of_bilinear (𝕜 := ℝ)
      (E := PeriodicHolderHalf) (F := PeriodicHolderHalf) (G := PeriodicHolderHalf) (G' := PeriodicC1HolderHalf)
      holderProductRealCLM
      (DifferentiableAt.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) tangent)
      (DifferentiableAt.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) conjugated)
    exact HasFDerivAt.differentiableAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) derivative
  exact DifferentiableAt.const_smul (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf)
    (R := ℂ) product (-(1 / (4 * Real.pi) : ℂ))

end

end EulerNonuniqueness.Paper
