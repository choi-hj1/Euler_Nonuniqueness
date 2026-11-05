import EulerNonuniqueness.General.LocalSecondRegularity

open Filter
open scoped Topology

namespace EulerNonuniqueness.General

noncomputable section

variable {Domain Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem hasLipschitzSecondDerivativeNear_of_derivative_field
    {function : Domain → Target} {field : Domain → Domain →L[ℝ] Target} {point : Domain}
    (actual : ∀ᶠ current in 𝓝 point, HasFDerivAt function (field current) current)
    (regular : HasLipschitzDerivativeNear field point) :
    HasLipschitzSecondDerivativeNear function point := by
  have equal : fderiv ℝ function =ᶠ[𝓝 point] field := actual.mono fun _ derivative => derivative.fderiv
  have derivativeRegular := regular.congr equal
  exact ⟨⟨actual.mono fun _ derivative => derivative.differentiableAt,
    derivativeRegular.lipschitzNear⟩, derivativeRegular⟩

end

end EulerNonuniqueness.General
