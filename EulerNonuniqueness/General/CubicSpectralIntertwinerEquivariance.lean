import EulerNonuniqueness.General.CubicSpectralIntertwiner

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem cubicSpectralIntertwiner_equivariant (linear first second reference : Space →L[ℝ] Space)
    (firstIntertwines : first.comp linear = linear.comp second)
    (referenceCommutes : reference.comp linear = linear.comp reference) :
    (cubicSpectralIntertwiner first reference).comp linear =
      linear.comp (cubicSpectralIntertwiner second reference) := by
  have firstAction (value : Space) : first (linear value) = linear (second value) :=
    congrArg (fun operator : Space →L[ℝ] Space => operator value) firstIntertwines
  have referenceAction (value : Space) : reference (linear value) = linear (reference value) :=
    congrArg (fun operator : Space →L[ℝ] Space => operator value) referenceCommutes
  apply ContinuousLinearMap.ext
  intro value
  simp only [cubicSpectralIntertwiner, cubicSpectralProjection, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_add, map_sub, map_smul, firstAction, referenceAction]

end EulerNonuniqueness.General
