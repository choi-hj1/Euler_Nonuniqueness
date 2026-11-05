import EulerNonuniqueness.Section6.MovingPatchFamilyQuadrupole
import EulerNonuniqueness.Section6.PaperReferenceShapeForcing

noncomputable section

namespace EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison

def withQuadrupoleReceivers {count : ℕ} (comparison : MovingPatchFamilySourceComparison (count * 4))
    (receiver : Fin count) (radius : ℝ) (nonnegative : 0 ≤ radius) : MovingPatchFamilySourceComparison (count * 4) :=
  {comparison with
    firstReceiver := fun current => quadrupoleCenter comparison.first.patchMotion current receiver
    secondReceiver := fun current => quadrupoleCenter comparison.second.patchMotion current receiver
    receiverRadius := radius
    receiverRadius_nonnegative := nonnegative}

theorem withQuadrupoleReceivers_quadrupole {count : ℕ}
    (comparison : MovingPatchFamilySourceComparison (count * 4)) (receiver source : Fin count)
    (radius : ℝ) (nonnegative : 0 ≤ radius) :
    (comparison.withQuadrupoleReceivers receiver radius nonnegative).quadrupole source =
      {comparison.quadrupole source with
        firstReceiver := fun current => quadrupoleCenter comparison.first.patchMotion current receiver
        secondReceiver := fun current => quadrupoleCenter comparison.second.patchMotion current receiver
        receiverRadius := radius
        receiverRadius_nonnegative := nonnegative} := rfl

end EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison
