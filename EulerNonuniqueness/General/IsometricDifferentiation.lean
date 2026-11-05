import EulerNonuniqueness.Section3.ClosedSubmoduleDerivative
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.MetricSpace.Antilipschitz

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {domain source target : Type*}
  [NormedAddCommGroup domain] [NormedSpace ℝ domain]
  [NormedAddCommGroup source] [NormedSpace ℝ source] [CompleteSpace source]
  [NormedAddCommGroup target] [NormedSpace ℝ target]

theorem differentiableAt_of_linearIsometry_comp (embedding : source →ₗᵢ[ℝ] target)
    {function : domain → source} {point : domain}
    (ambient : DifferentiableAt ℝ (fun current => embedding (function current)) point) :
    DifferentiableAt ℝ function point := by
  let subspace := LinearMap.range embedding.toLinearMap
  have closed : IsClosed (subspace : Set target) :=
    embedding.isometry.antilipschitz.isClosed_range embedding.isometry.uniformContinuous
  let rangeFunction : domain → subspace := fun current => ⟨embedding (function current), ⟨function current, rfl⟩⟩
  have rangeDerivative := Paper.hasFDerivAt_closedSubmodule subspace closed
    (function := rangeFunction) ambient.hasFDerivAt
  let inverse : subspace →L[ℝ] source := embedding.equivRange.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have derivative := inverse.hasFDerivAt.comp point rangeDerivative
  have equality : (inverse ∘ rangeFunction) = function := by
    funext current
    change embedding.equivRange.symm (embedding.equivRange (function current)) = function current
    exact embedding.equivRange.symm_apply_apply (function current)
  rw [equality] at derivative
  exact derivative.differentiableAt

end EulerNonuniqueness.General
