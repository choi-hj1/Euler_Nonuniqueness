import EulerNonuniqueness.General.IsometricLocalDerivativeLipschitz
import EulerNonuniqueness.General.LocalSecondRegularity

open Filter
open scoped Topology

namespace EulerNonuniqueness.General

noncomputable section

variable {Domain Source Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Source] [NormedSpace ℝ Source] [CompleteSpace Source]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem hasLipschitzSecondDerivativeNear_of_linearIsometry_comp
    (embedding : Source →ₗᵢ[ℝ] Target) {function : Domain → Source} {point : Domain}
    (regular : HasLipschitzSecondDerivativeNear (fun current => embedding (function current)) point) :
    HasLipschitzSecondDerivativeNear function point := by
  have first := hasLipschitzDerivativeNear_of_linearIsometry_comp embedding regular.1
  have equal : (fun current => operatorPostcompIsometry embedding (fderiv ℝ function current))
      =ᶠ[𝓝 point] fderiv ℝ (fun current => embedding (function current)) := by
    filter_upwards [first.1] with current derivative
    exact (embedding.toContinuousLinearMap.hasFDerivAt.comp current derivative.hasFDerivAt).fderiv.symm
  have image := regular.2.congr equal
  exact ⟨first, hasLipschitzDerivativeNear_of_linearIsometry_comp
    (operatorPostcompIsometry embedding) image⟩

end

end EulerNonuniqueness.General
