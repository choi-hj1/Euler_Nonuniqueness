import EulerNonuniqueness.General.SpectralTubularChart

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem spectralTubularChart_equivariant
    (projection linear : Space →L[ℝ] Space) (operator : Space → Space →L[ℝ] Space)
    (projectionCommutes : ∀ value, projection (linear value) = linear (projection value))
    (operatorIntertwines : ∀ value, (operator (linear value)).comp linear = linear.comp (operator value))
    (value : Space) :
    spectralTubularChart projection operator (linear value) =
      linear (spectralTubularChart projection operator value) := by
  have intertwines := congrArg (fun current : Space →L[ℝ] Space => current (value - projection value))
    (operatorIntertwines value)
  simp only [ContinuousLinearMap.comp_apply] at intertwines
  simp only [spectralTubularChart, projectionCommutes, ← map_sub, intertwines, map_add]

end EulerNonuniqueness.General
