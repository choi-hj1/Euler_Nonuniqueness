import EulerNonuniqueness.Section6.MovingQuadrupoleCentroidResponse
import EulerNonuniqueness.Section6.MovingPatchFamilySourceComparison

noncomputable section

namespace EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem receivingCentroidResponse_difference {count : ℕ}
    (comparison : MovingPatchFamilySourceComparison count) (receiver : Fin count)
    (firstCenter : comparison.firstReceiver = (comparison.first.patch receiver).center)
    (secondCenter : comparison.secondReceiver = (comparison.second.patch receiver).center)
    (physicalRadius : comparison.receiverRadius = (comparison.first.patch receiver).radius) :
    comparison.first.receivingCentroidResponse receiver comparison.time -
        comparison.second.receivingCentroidResponse receiver comparison.time =
      comparison.receiverRadius •
        ((Circle.exp ((comparison.first.patch receiver).phase comparison.time) : ℂ) *
          contourExteriorCentroidResponse (Circle.exp ((comparison.first.patch receiver).phase comparison.time))
            (fun power => comparison.first.exteriorTaylorCoefficient (Finset.univ.erase receiver)
              comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time)
            ((comparison.first.patch receiver).shape comparison.time)) -
      comparison.receiverRadius •
        ((Circle.exp ((comparison.first.patch receiver).phase comparison.time) : ℂ) *
          contourExteriorCentroidResponse (Circle.exp ((comparison.first.patch receiver).phase comparison.time))
            (fun power => comparison.second.exteriorTaylorCoefficient (Finset.univ.erase receiver)
              comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time)
            ((comparison.second.patch receiver).shape comparison.time)) := by
  unfold FiniteMovingPatchFamily.receivingCentroidResponse
  rw [firstCenter, secondCenter, physicalRadius, ← comparison.radiusEqual receiver,
    ← comparison.phaseEqual receiver]

end EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison
