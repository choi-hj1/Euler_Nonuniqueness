import EulerNonuniqueness.Section3.PeriodicHilbertSpectral

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

local instance flowHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance flowC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance flowC1Module : Module ℂ PeriodicC1HolderHalf := Submodule.module complexPeriodicC1HolderGraph
local instance flowC1ComplexSpace : NormedSpace ℂ PeriodicC1HolderHalf := complexC1HolderNormedSpace
local instance flowC1RealBoundedSMul : IsBoundedSMul ℝ PeriodicC1HolderHalf :=
  NormedSpace.isBoundedSMul (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
local instance flowC1ComplexBoundedSMul : IsBoundedSMul ℂ PeriodicC1HolderHalf :=
  NormedSpace.isBoundedSMul (𝕜 := ℂ) (E := PeriodicC1HolderHalf)
local instance flowC1ContinuousAdd : ContinuousAdd PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousAdd
local instance flowC1UniformAdd : IsUniformAddGroup PeriodicC1HolderHalf :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf)
local instance flowOperatorTopology : TopologicalSpace (PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.topologicalSpace (𝕜₁ := ℂ) (𝕜₂ := ℂ) (σ := RingHom.id ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
local instance flowOperatorGroup : SeminormedAddCommGroup (PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance flowOperatorSpace : NormedSpace ℂ (PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℂ)

def periodicHilbertFlow (time : ℝ) (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  periodicMeanProjectionCCLM data + Real.cos (time / 2) • periodicMeanZeroPartCCLM data +
    (-Real.sin (time / 2)) • periodicHilbertC1 data

def periodicHilbertFlowCCLM (time : ℝ) : PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf :=
  periodicMeanProjectionCCLM + (Real.cos (time / 2) : ℂ) • periodicMeanZeroPartCCLM +
    (-Real.sin (time / 2) : ℂ) • periodicHilbertC1CCLM

theorem periodicHilbertFlowCCLM_apply (time : ℝ) (data : PeriodicC1HolderHalf) :
    periodicHilbertFlowCCLM time data = periodicHilbertFlow time data := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (periodicMeanProjectionCCLM data).val.1 label +
      (Real.cos (time / 2) : ℂ) * (periodicMeanZeroPartCCLM data).val.1 label +
      (-Real.sin (time / 2) : ℂ) * (periodicHilbertC1 data).val.1 label =
    (periodicMeanProjectionCCLM data).val.1 label +
      Real.cos (time / 2) • (periodicMeanZeroPartCCLM data).val.1 label +
      (-Real.sin (time / 2)) • (periodicHilbertC1 data).val.1 label
  simp only [Complex.real_smul, Complex.ofReal_neg]

theorem periodicHilbertFlow_zero (data : PeriodicC1HolderHalf) : periodicHilbertFlow 0 data = data := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (periodicMeanProjectionCCLM data).val.1 label +
      Real.cos (0 / 2) • (data.val.1 label - (periodicMeanProjectionCCLM data).val.1 label) +
      (-Real.sin (0 / 2)) • (periodicHilbertC1 data).val.1 label = _
  simp only [zero_div, Real.cos_zero, Real.sin_zero, neg_zero, one_smul, zero_smul, add_zero]
  ring

theorem c1AngularIntegral_smul_real (scalar : ℝ) (data : PeriodicC1HolderHalf) :
    c1AngularIntegralCCLM (scalar • data) = scalar • c1AngularIntegralCCLM data := by
  change (∫ label in (0 : ℝ)..(2 * Real.pi), scalar • data.val.1 label) = _
  exact intervalIntegral.integral_smul scalar _

theorem periodicHilbertFlow_integral (time : ℝ) (data : PeriodicC1HolderHalf) :
    c1AngularIntegralCCLM (periodicHilbertFlow time data) = c1AngularIntegralCCLM data := by
  unfold periodicHilbertFlow
  rw [c1AngularIntegral_add, c1AngularIntegral_add, c1AngularIntegral_smul_real,
    c1AngularIntegral_smul_real, periodicMeanProjectionCCLM_integral,
    periodicMeanZeroPartCCLM_integral, c1AngularIntegral_hilbert, smul_zero, smul_zero, add_zero, add_zero]

theorem periodicHilbertFlow_mean (time : ℝ) (data : PeriodicC1HolderHalf) :
    periodicMeanProjectionCCLM (periodicHilbertFlow time data) = periodicMeanProjectionCCLM data := by
  rw [periodicMeanProjectionCCLM_eq_constant, periodicHilbertFlow_integral,
    ← periodicMeanProjectionCCLM_eq_constant]

theorem periodicHilbertFlow_meanZeroPart (time : ℝ) (data : PeriodicC1HolderHalf) :
    periodicMeanZeroPartCCLM (periodicHilbertFlow time data) =
      Real.cos (time / 2) • periodicMeanZeroPartCCLM data +
        (-Real.sin (time / 2)) • periodicHilbertC1 data := by
  change periodicHilbertFlow time data - periodicMeanProjectionCCLM (periodicHilbertFlow time data) = _
  rw [periodicHilbertFlow_mean]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change ((periodicMeanProjectionCCLM data).val.1 label +
      Real.cos (time / 2) • (periodicMeanZeroPartCCLM data).val.1 label +
      (-Real.sin (time / 2)) • (periodicHilbertC1 data).val.1 label) -
      (periodicMeanProjectionCCLM data).val.1 label =
    Real.cos (time / 2) • (periodicMeanZeroPartCCLM data).val.1 label +
      (-Real.sin (time / 2)) • (periodicHilbertC1 data).val.1 label
  simp only [Complex.real_smul]
  ring

theorem periodicHilbertC1_flow (time : ℝ) (data : PeriodicC1HolderHalf) :
    periodicHilbertC1 (periodicHilbertFlow time data) =
      Real.cos (time / 2) • periodicHilbertC1 data +
        Real.sin (time / 2) • periodicMeanZeroPartCCLM data := by
  unfold periodicHilbertFlow
  rw [periodicHilbertC1_add, periodicHilbertC1_add, periodicHilbertC1_smul,
    periodicHilbertC1_smul, periodicHilbertC1_meanProjection,
    periodicHilbertC1_meanZeroPart, periodicHilbertC1_sq]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (0 + Real.cos (time / 2) • (periodicHilbertC1 data).val.1 label) +
      (-Real.sin (time / 2)) • (-(periodicMeanZeroPartCCLM data).val.1 label) =
    Real.cos (time / 2) • (periodicHilbertC1 data).val.1 label +
      Real.sin (time / 2) • (periodicMeanZeroPartCCLM data).val.1 label
  simp only [Complex.real_smul]
  push_cast
  ring

theorem periodicHilbertFlow_add (firstTime secondTime : ℝ) (data : PeriodicC1HolderHalf) :
    periodicHilbertFlow firstTime (periodicHilbertFlow secondTime data) =
      periodicHilbertFlow (firstTime + secondTime) data := by
  change periodicMeanProjectionCCLM (periodicHilbertFlow secondTime data) +
    Real.cos (firstTime / 2) • periodicMeanZeroPartCCLM (periodicHilbertFlow secondTime data) +
    (-Real.sin (firstTime / 2)) • periodicHilbertC1 (periodicHilbertFlow secondTime data) = _
  rw [periodicHilbertFlow_mean, periodicHilbertFlow_meanZeroPart, periodicHilbertC1_flow]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change ((periodicMeanProjectionCCLM data).val.1 label +
      Real.cos (firstTime / 2) • (Real.cos (secondTime / 2) • (periodicMeanZeroPartCCLM data).val.1 label +
        (-Real.sin (secondTime / 2)) • (periodicHilbertC1 data).val.1 label)) +
      (-Real.sin (firstTime / 2)) • (Real.cos (secondTime / 2) • (periodicHilbertC1 data).val.1 label +
        Real.sin (secondTime / 2) • (periodicMeanZeroPartCCLM data).val.1 label) =
    (periodicMeanProjectionCCLM data).val.1 label +
      Real.cos ((firstTime + secondTime) / 2) • (periodicMeanZeroPartCCLM data).val.1 label +
      (-Real.sin ((firstTime + secondTime) / 2)) • (periodicHilbertC1 data).val.1 label
  rw [show (firstTime + secondTime) / 2 = firstTime / 2 + secondTime / 2 by ring,
    Real.cos_add, Real.sin_add]
  simp only [Complex.real_smul]
  push_cast
  ring

end

end EulerNonuniqueness.Paper
