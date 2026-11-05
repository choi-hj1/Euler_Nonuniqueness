import EulerNonuniqueness.General.SpectralHomologicalBlock

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℂ Space]

theorem linearHomologicalOperator_intertwines (transport : Space →ₗ[ℂ] Space)
    (source target sourceCorrection targetCorrection : Space →L[ℂ] Space)
    (generatorIntertwines : ∀ vector, target (transport vector) = transport (source vector))
    (correctionIntertwines : ∀ vector, targetCorrection (transport vector) = transport (sourceCorrection vector))
    (frequency : ℂ) (vector : Space) :
    linearHomologicalOperator target frequency targetCorrection (transport vector) =
      transport (linearHomologicalOperator source frequency sourceCorrection vector) := by
  simp only [linearHomologicalOperator, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  rw [generatorIntertwines, correctionIntertwines, correctionIntertwines, generatorIntertwines,
    map_sub, map_add, map_smul]

end EulerNonuniqueness.General
