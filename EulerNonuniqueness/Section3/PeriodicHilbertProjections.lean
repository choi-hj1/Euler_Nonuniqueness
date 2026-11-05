import EulerNonuniqueness.Section3.PeriodicHilbertMeanZero

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

local instance projectionHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance projectionC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance projectionC1Module : Module ℂ PeriodicC1HolderHalf := Submodule.module complexPeriodicC1HolderGraph
local instance projectionC1ComplexSpace : NormedSpace ℂ PeriodicC1HolderHalf := complexC1HolderNormedSpace
local instance projectionC1BoundedSMul : IsBoundedSMul ℂ PeriodicC1HolderHalf :=
  NormedSpace.isBoundedSMul (𝕜 := ℂ) (E := PeriodicC1HolderHalf)
local instance projectionC1ContinuousAdd : ContinuousAdd PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousAdd
local instance projectionC1UniformAdd : IsUniformAddGroup PeriodicC1HolderHalf :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf)
local instance projectionOperatorTopology : TopologicalSpace (PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.topologicalSpace (𝕜₁ := ℂ) (𝕜₂ := ℂ) (σ := RingHom.id ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
local instance projectionOperatorGroup : SeminormedAddCommGroup (PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance projectionOperatorSpace : NormedSpace ℂ (PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℂ)

def periodicHilbertPositiveProjection : PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf :=
  (1 / 2 : ℂ) • (periodicMeanZeroPartCCLM + Complex.I • periodicHilbertC1CCLM)

def periodicHilbertNegativeProjection : PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf :=
  (1 / 2 : ℂ) • (periodicMeanZeroPartCCLM - Complex.I • periodicHilbertC1CCLM)

theorem periodicHilbertPositiveProjection_apply (data : PeriodicC1HolderHalf) :
    periodicHilbertPositiveProjection data =
      (1 / 2 : ℂ) • (periodicMeanZeroPartCCLM data + Complex.I • periodicHilbertC1 data) := rfl

theorem periodicHilbertNegativeProjection_apply (data : PeriodicC1HolderHalf) :
    periodicHilbertNegativeProjection data =
      (1 / 2 : ℂ) • (periodicMeanZeroPartCCLM data - Complex.I • periodicHilbertC1 data) := rfl

theorem periodicHilbertC1_positiveProjection (data : PeriodicC1HolderHalf) :
    periodicHilbertC1 (periodicHilbertPositiveProjection data) =
      (-Complex.I) • periodicHilbertPositiveProjection data := by
  rw [periodicHilbertPositiveProjection_apply, periodicHilbertC1_smul_complex,
    periodicHilbertC1_add, periodicHilbertC1_smul_complex,
    periodicHilbertC1_meanZeroPart, periodicHilbertC1_sq]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (1 / 2 : ℂ) * ((periodicHilbertC1 data).val.1 label +
      Complex.I * (-(periodicMeanZeroPartCCLM data).val.1 label)) =
    (-Complex.I) * ((1 / 2 : ℂ) * ((periodicMeanZeroPartCCLM data).val.1 label +
      Complex.I * (periodicHilbertC1 data).val.1 label))
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem periodicHilbertC1_negativeProjection (data : PeriodicC1HolderHalf) :
    periodicHilbertC1 (periodicHilbertNegativeProjection data) =
      Complex.I • periodicHilbertNegativeProjection data := by
  have subtraction (first second : PeriodicC1HolderHalf) :
      periodicHilbertC1 (first - second) = periodicHilbertC1 first - periodicHilbertC1 second := by
    have decomposition : first - second = first + (-1 : ℂ) • second := by
      apply PeriodicC1HolderHalf.ext_value
      intro label
      change first.val.1 label - second.val.1 label = first.val.1 label + (-1 : ℂ) * second.val.1 label
      ring
    rw [decomposition, periodicHilbertC1_add, periodicHilbertC1_smul_complex]
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change (periodicHilbertC1 first).val.1 label + (-1 : ℂ) * (periodicHilbertC1 second).val.1 label =
      (periodicHilbertC1 first).val.1 label - (periodicHilbertC1 second).val.1 label
    ring
  rw [periodicHilbertNegativeProjection_apply, periodicHilbertC1_smul_complex,
    subtraction, periodicHilbertC1_smul_complex, periodicHilbertC1_meanZeroPart, periodicHilbertC1_sq]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (1 / 2 : ℂ) * ((periodicHilbertC1 data).val.1 label -
      Complex.I * (-(periodicMeanZeroPartCCLM data).val.1 label)) =
    Complex.I * ((1 / 2 : ℂ) * ((periodicMeanZeroPartCCLM data).val.1 label -
      Complex.I * (periodicHilbertC1 data).val.1 label))
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem periodicHilbertProjections_sum (data : PeriodicC1HolderHalf) :
    periodicHilbertPositiveProjection data + periodicHilbertNegativeProjection data =
      periodicMeanZeroPartCCLM data := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (1 / 2 : ℂ) * ((periodicMeanZeroPartCCLM data).val.1 label +
      Complex.I * (periodicHilbertC1 data).val.1 label) +
    (1 / 2 : ℂ) * ((periodicMeanZeroPartCCLM data).val.1 label -
      Complex.I * (periodicHilbertC1 data).val.1 label) = _
  ring

end

end EulerNonuniqueness.Paper
