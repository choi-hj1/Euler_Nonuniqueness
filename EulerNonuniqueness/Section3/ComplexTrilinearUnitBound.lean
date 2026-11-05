import EulerNonuniqueness.Section3.ComplexOperatorUnitBound
import Mathlib.Analysis.NormedSpace.OperatorNorm.Bilinear

namespace EulerNonuniqueness.General

noncomputable section

variable {First Second Third Target : Type*}
  [NormedAddCommGroup First] [NormedSpace ℂ First]
  [NormedAddCommGroup Second] [NormedSpace ℂ Second]
  [NormedAddCommGroup Third] [NormedSpace ℂ Third]
  [NormedAddCommGroup Target] [NormedSpace ℂ Target]

local instance trilinearThirdGroup : NormedAddCommGroup (Third →L[ℂ] Target) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ) (E := Third) (F := Target) (σ₁₂ := RingHom.id ℂ)
local instance trilinearThirdModule : Module ℂ (Third →L[ℂ] Target) :=
  ContinuousLinearMap.module (R := ℂ) (R₃ := ℂ) (S₃ := ℂ) (M := Third) (M₃ := Target) (σ₁₃ := RingHom.id ℂ)
local instance trilinearThirdSpace : NormedSpace ℂ (Third →L[ℂ] Target) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ) (E := Third) (F := Target) (σ₁₂ := RingHom.id ℂ)
local instance trilinearSecondGroup : NormedAddCommGroup (Second →L[ℂ] Third →L[ℂ] Target) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ) (E := Second) (F := Third →L[ℂ] Target) (σ₁₂ := RingHom.id ℂ)
local instance trilinearSecondModule : Module ℂ (Second →L[ℂ] Third →L[ℂ] Target) :=
  ContinuousLinearMap.module (R := ℂ) (R₃ := ℂ) (S₃ := ℂ) (M := Second) (M₃ := Third →L[ℂ] Target) (σ₁₃ := RingHom.id ℂ)
local instance trilinearSecondSpace : NormedSpace ℂ (Second →L[ℂ] Third →L[ℂ] Target) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ) (E := Second) (F := Third →L[ℂ] Target) (σ₁₂ := RingHom.id ℂ)
local instance trilinearFirstGroup : NormedAddCommGroup (First →L[ℂ] Second →L[ℂ] Third →L[ℂ] Target) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ) (E := First)
    (F := Second →L[ℂ] Third →L[ℂ] Target) (σ₁₂ := RingHom.id ℂ)

theorem complex_trilinear_norm_le_of_unit_norm
    (operator : First →L[ℂ] Second →L[ℂ] Third →L[ℂ] Target) {bound : ℝ}
    (nonnegative : 0 ≤ bound)
    (estimate : ∀ first, ‖first‖ = 1 → ∀ second, ‖second‖ = 1 →
      ∀ third, ‖third‖ = 1 → ‖operator first second third‖ ≤ bound) : ‖operator‖ ≤ bound := by
  apply complex_opNorm_le_of_unit_norm operator nonnegative
  intro first firstNorm
  apply complex_opNorm_le_of_unit_norm (operator first) nonnegative
  intro second secondNorm
  exact complex_opNorm_le_of_unit_norm (operator first second) nonnegative
    (estimate first firstNorm second secondNorm)

end

end EulerNonuniqueness.General
