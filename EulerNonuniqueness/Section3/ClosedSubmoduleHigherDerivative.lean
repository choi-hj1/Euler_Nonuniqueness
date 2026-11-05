import EulerNonuniqueness.General.IsometricDifferentiation

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

variable {domain ambient : Type*}
  [NormedAddCommGroup domain] [NormedSpace ℝ domain]
  [NormedAddCommGroup ambient] [NormedSpace ℝ ambient] [CompleteSpace ambient]

def closedSubmoduleOperatorEmbedding (subspace : Submodule ℝ ambient) :
    (domain →L[ℝ] subspace) →ₗᵢ[ℝ] (domain →L[ℝ] ambient) where
  toFun derivative := subspace.subtypeL.comp derivative
  map_add' first second := by
    apply ContinuousLinearMap.ext
    intro direction
    rfl
  map_smul' scalar derivative := by
    apply ContinuousLinearMap.ext
    intro direction
    rfl
  norm_map' derivative := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg derivative)
      intro direction
      exact derivative.le_opNorm direction
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (subspace.subtypeL.comp derivative))
      intro direction
      exact (subspace.subtypeL.comp derivative).le_opNorm direction

theorem closedSubmoduleOperatorEmbedding_apply (subspace : Submodule ℝ ambient)
    (derivative : domain →L[ℝ] subspace) :
    closedSubmoduleOperatorEmbedding subspace derivative = subspace.subtypeL.comp derivative := rfl

theorem closedSubmoduleOperatorEmbedding_fderiv (subspace : Submodule ℝ ambient)
    {function : domain → subspace} {point : domain} (differentiable : DifferentiableAt ℝ function point) :
    closedSubmoduleOperatorEmbedding subspace (fderiv ℝ function point) =
      fderiv ℝ (fun argument => (function argument : ambient)) point := by
  have derivative := subspace.subtypeL.hasFDerivAt.comp point differentiable.hasFDerivAt
  exact derivative.fderiv.symm

theorem differentiableAt_fderiv_closedSubmodule (subspace : Submodule ℝ ambient)
    (closed : IsClosed (subspace : Set ambient)) {function : domain → subspace} {point : domain}
    (nearby : ∀ᶠ current in 𝓝 point, DifferentiableAt ℝ function current)
    (ambientDerivative : DifferentiableAt ℝ
      (fun current => fderiv ℝ (fun argument => (function argument : ambient)) current) point) :
    DifferentiableAt ℝ (fun current => fderiv ℝ function current) point := by
  letI : CompleteSpace subspace := closed.completeSpace_coe
  let embedding : (domain →L[ℝ] subspace) →ₗᵢ[ℝ] (domain →L[ℝ] ambient) :=
    closedSubmoduleOperatorEmbedding subspace
  have equality : (fun current => closedSubmoduleOperatorEmbedding subspace (fderiv ℝ function current)) =ᶠ[𝓝 point]
      (fun current => fderiv ℝ (fun argument => (function argument : ambient)) current) := by
    filter_upwards [nearby] with current differentiable
    exact closedSubmoduleOperatorEmbedding_fderiv subspace differentiable
  have embeddedDerivative : DifferentiableAt ℝ
      (fun current => closedSubmoduleOperatorEmbedding subspace (fderiv ℝ function current)) point :=
    DifferentiableAt.congr_of_eventuallyEq (𝕜 := ℝ) (E := domain) (F := domain →L[ℝ] ambient)
      ambientDerivative equality
  exact General.differentiableAt_of_linearIsometry_comp (domain := domain)
    (source := domain →L[ℝ] subspace) (target := domain →L[ℝ] ambient)
    (function := fun current => fderiv ℝ function current) (point := point) embedding embeddedDerivative

end EulerNonuniqueness.Paper
