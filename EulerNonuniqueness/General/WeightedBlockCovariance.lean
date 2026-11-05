import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm.Bilinear

namespace EulerNonuniqueness.General

noncomputable section

variable {Space Target : Type*} [NormedAddCommGroup Space] [NormedSpace ℂ Space]
  [NormedAddCommGroup Target] [NormedSpace ℂ Target]

def weightedOperatorBlock (receiver : Target →L[ℂ] Space) (operator : Target →L[ℂ] Target)
    (source : Space →L[ℂ] Target) : Space →L[ℂ] Space := receiver.comp (operator.comp source)

theorem weightedOperatorBlock_covariance (receiver : Target →L[ℂ] Space) (operator : Target →L[ℂ] Target)
    (source : Space →L[ℂ] Target) (action : Space →L[ℂ] Space) (targetAction : Target →L[ℂ] Target)
    (weight : ℂ) (receiverIdentity : ∀ vector, action (receiver vector) = receiver (targetAction vector))
    (sourceIdentity : ∀ vector, targetAction (source vector) = source (action vector))
    (operatorIdentity : ∀ vector, targetAction (operator vector) = weight • operator (targetAction vector))
    (vector : Space) : action (weightedOperatorBlock receiver operator source vector) =
      weight • weightedOperatorBlock receiver operator source (action vector) := by
  change action (receiver (operator (source vector))) = weight • receiver (operator (source (action vector)))
  rw [receiverIdentity, operatorIdentity, map_smul, sourceIdentity]

end

end EulerNonuniqueness.General
