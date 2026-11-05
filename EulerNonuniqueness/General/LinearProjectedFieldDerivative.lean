import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem linear_projected_field_hasDerivAt
    (projection : Space →L[ℝ] Space) (field : Space → Space)
    {trajectory : ℝ → Space} {time : ℝ} {forcing : Space}
    (equation : HasDerivAt trajectory (field (trajectory time) + forcing) time) :
    HasDerivAt (fun current => projection (trajectory current))
      (projection (field (trajectory time)) + projection forcing) time := by
  have derivative : HasFDerivAt (projection : Space → Space) projection (trajectory time) :=
    ContinuousLinearMap.hasFDerivAt projection
  simpa only [map_add] using HasFDerivAt.comp_hasDerivAt (E := Space) (F := Space)
    (f := trajectory) time derivative equation

end EulerNonuniqueness.General
