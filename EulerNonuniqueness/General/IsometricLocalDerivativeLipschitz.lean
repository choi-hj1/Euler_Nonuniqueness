import EulerNonuniqueness.General.IsometricDifferentiation
import EulerNonuniqueness.Section3.LocalDerivativeLipschitzCalculus

open Filter Set
open scoped Topology

namespace EulerNonuniqueness.General

noncomputable section

variable {Domain Source Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Source] [NormedSpace ℝ Source] [CompleteSpace Source]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

def operatorPostcompIsometry (embedding : Source →ₗᵢ[ℝ] Target) :
    (Domain →L[ℝ] Source) →ₗᵢ[ℝ] (Domain →L[ℝ] Target) where
  toFun derivative := embedding.toContinuousLinearMap.comp derivative
  map_add' first second := by ext direction; simp
  map_smul' scalar derivative := by ext direction; simp
  norm_map' derivative := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg derivative)
      intro direction
      change ‖embedding (derivative direction)‖ ≤ ‖derivative‖ * ‖direction‖
      rw [embedding.norm_map]
      exact derivative.le_opNorm direction
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro direction
      have bound := (embedding.toContinuousLinearMap.comp derivative).le_opNorm direction
      simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
        embedding.norm_map] using bound

theorem hasLipschitzDerivativeNear_of_linearIsometry_comp
    (embedding : Source →ₗᵢ[ℝ] Target) {function : Domain → Source} {point : Domain}
    (regular : HasLipschitzDerivativeNear (fun current => embedding (function current)) point) :
    HasLipschitzDerivativeNear function point := by
  have differentiable : ∀ᶠ current in 𝓝 point, DifferentiableAt ℝ function current :=
    regular.1.mono fun current derivative => differentiableAt_of_linearIsometry_comp embedding derivative
  have equality : ∀ᶠ current in 𝓝 point,
      operatorPostcompIsometry embedding (fderiv ℝ function current) =
        fderiv ℝ (fun current => embedding (function current)) current := by
    filter_upwards [differentiable] with current derivative
    exact (embedding.toContinuousLinearMap.hasFDerivAt.comp current derivative.hasFDerivAt).fderiv.symm
  refine ⟨differentiable, ?_⟩
  obtain ⟨constant, neighborhood, nearby, lipschitz⟩ := regular.2
  refine ⟨constant, neighborhood ∩ {current | operatorPostcompIsometry embedding
    (fderiv ℝ function current) = fderiv ℝ (fun current => embedding (function current)) current},
    inter_mem nearby equality, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro initial initialInside final finalInside
  rw [← (operatorPostcompIsometry embedding).isometry.dist_eq,
    initialInside.2, finalInside.2]
  exact lipschitz.dist_le_mul initial initialInside.1 final finalInside.1

end

end EulerNonuniqueness.General
