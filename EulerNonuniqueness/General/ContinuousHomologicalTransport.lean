import EulerNonuniqueness.General.LinearHomologicalTransport

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℂ Space]

theorem linearHomologicalOperator_intertwines_continuous (transport : Space →L[ℂ] Space)
    (source target sourceCorrection targetCorrection : Space →L[ℂ] Space)
    (generatorIntertwines : ∀ vector, target (transport vector) = transport (source vector))
    (correctionIntertwines : ∀ vector, targetCorrection (transport vector) = transport (sourceCorrection vector))
    (frequency : ℂ) (vector : Space) :
    linearHomologicalOperator target frequency targetCorrection (transport vector) =
      transport (linearHomologicalOperator source frequency sourceCorrection vector) :=
  linearHomologicalOperator_intertwines transport.toLinearMap source target sourceCorrection targetCorrection
    generatorIntertwines correctionIntertwines frequency vector

end EulerNonuniqueness.General
