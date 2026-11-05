import EulerNonuniqueness.Section3.ContourTangentInnerJet

open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance tangentInnerDerivativeHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance tangentInnerDerivativeC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance tangentInnerDerivativeOperatorGroup : SeminormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance tangentInnerDerivativeOperatorComplexSpace : NormedSpace ℂ (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)

def contourTangentInnerDerivativeCLM (data : PeriodicC1HolderHalf) {radius : ℝ}
    (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) : PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf :=
  (contourCauchyJointDerivativeCLM data (extendedContourTangentQuotient data) near small).comp
      ((ContinuousLinearMap.id ℝ PeriodicC1HolderHalf).prod (contourQuotientDerivativeCLM data)) +
    ((Real.pi : ℂ) * Complex.I) • contourQuotientDerivativeCLM data

theorem contourTangentInnerLinear_eq_derivative (data increment : PeriodicC1HolderHalf)
    {radius : ℝ} (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    contourTangentInnerLinear data increment = contourTangentInnerDerivativeCLM data near small increment := by
  unfold contourTangentInnerLinear
  rw [extendedContourCauchy_eq data (contourQuotientDerivativeCLM data increment) (near.trans small)]
  rfl

theorem hasFDerivAt_contourTangentInner (data : PeriodicC1HolderHalf) {radius : ℝ}
    (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    HasFDerivAt contourTangentInner (contourTangentInnerDerivativeCLM data near small) data := by
  have quotient : HasFDerivAt extendedContourTangentQuotient (contourQuotientDerivativeCLM data) data := by
    exact hasFDerivAt_extendedContourTangentQuotient data (near.trans small)
  let pairMap : PeriodicC1HolderHalf →L[ℝ] (PeriodicC1HolderHalf × PeriodicHolderHalf) :=
    (ContinuousLinearMap.id ℝ PeriodicC1HolderHalf).prod (contourQuotientDerivativeCLM data)
  have pair : HasFDerivAt (fun current : PeriodicC1HolderHalf =>
      (current, extendedContourTangentQuotient current)) pairMap data := by
    exact HasFDerivAt.prodMk (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
      (F := PeriodicC1HolderHalf) (G := PeriodicHolderHalf) (hasFDerivAt_id data) quotient
  have outer : HasFDerivAt
      (fun pair : PeriodicC1HolderHalf × PeriodicHolderHalf => extendedContourCauchy pair.1 pair.2)
      (contourCauchyJointDerivativeCLM data (extendedContourTangentQuotient data) near small)
      (data, extendedContourTangentQuotient data) := by
    exact hasFDerivAt_contourCauchy_joint data (extendedContourTangentQuotient data) near small
  have cauchy : HasFDerivAt (fun current : PeriodicC1HolderHalf =>
      extendedContourCauchy current (extendedContourTangentQuotient current))
      ((contourCauchyJointDerivativeCLM data (extendedContourTangentQuotient data) near small).comp pairMap) data := by
    exact HasFDerivAt.comp (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
      (F := PeriodicC1HolderHalf × PeriodicHolderHalf) (G := PeriodicHolderHalf)
      (f := fun current : PeriodicC1HolderHalf => (current, extendedContourTangentQuotient current))
      data outer pair
  have scaled : HasFDerivAt (fun current : PeriodicC1HolderHalf =>
      ((Real.pi : ℂ) * Complex.I) • extendedContourTangentQuotient current)
      (((Real.pi : ℂ) * Complex.I) • contourQuotientDerivativeCLM data) data := by
    exact HasFDerivAt.const_smul (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf)
      (R := ℂ) quotient ((Real.pi : ℂ) * Complex.I)
  exact HasFDerivAt.add (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) cauchy scaled

end

end EulerNonuniqueness.Paper
