import EulerNonuniqueness.General.ContinuousVectorSubmodule
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem continuousVectorSubmodule_bilinear (action : ℝ → Space →L[ℝ] Space)
    (bilinear : Space →L[ℝ] Space →L[ℝ] Space)
    (equivariant : ∀ parameter first second,
      action parameter (bilinear first second) = bilinear (action parameter first) (action parameter second))
    (first second : Space) (firstMember : first ∈ continuousVectorSubmodule action)
    (secondMember : second ∈ continuousVectorSubmodule action) :
    bilinear first second ∈ continuousVectorSubmodule action := by
  have firstOrbit : Continuous (fun parameter => action parameter first) := firstMember
  have secondOrbit : Continuous (fun parameter => action parameter second) := secondMember
  have composition : Continuous (fun parameter => bilinear (action parameter first) (action parameter second)) :=
    bilinear.isBoundedBilinearMap.continuous.comp (firstOrbit.prod_mk secondOrbit)
  change Continuous (fun parameter => action parameter (bilinear first second))
  simpa only [equivariant] using composition

end

end EulerNonuniqueness.General
