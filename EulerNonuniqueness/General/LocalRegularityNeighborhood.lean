import EulerNonuniqueness.Section3.LocalDerivativeLipschitzCalculus

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Domain Target : Type*} [PseudoMetricSpace Domain] [PseudoMetricSpace Target]

theorem LipschitzNear.eventually {function : Domain → Target} {point : Domain}
    (regular : LipschitzNear function point) :
    ∀ᶠ current in 𝓝 point, LipschitzNear function current := by
  obtain ⟨constant, neighborhood, nearby, lipschitz⟩ := regular
  have inside : point ∈ interior neighborhood := mem_interior_iff_mem_nhds.mpr nearby
  filter_upwards [isOpen_interior.mem_nhds inside] with current currentInside
  exact ⟨constant, neighborhood, mem_interior_iff_mem_nhds.mp currentInside, lipschitz⟩

variable {Space Range : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Range] [NormedSpace ℝ Range]

theorem HasLipschitzDerivativeNear.eventually {function : Space → Range} {point : Space}
    (regular : HasLipschitzDerivativeNear function point) :
    ∀ᶠ current in 𝓝 point, HasLipschitzDerivativeNear function current := by
  filter_upwards [regular.1.eventually_nhds, regular.2.eventually] with current differentiable derivativeLip
  exact ⟨differentiable, derivativeLip⟩

end EulerNonuniqueness.General
