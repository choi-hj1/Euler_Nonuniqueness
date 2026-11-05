import EulerNonuniqueness.Section6.MovingPatchSourceComparison
import EulerNonuniqueness.General.WeightedProjectionShapeBudget

noncomputable section

namespace EulerNonuniqueness.Paper.MovingPatchSourceComparison

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem spectralDifferenceBudget_le_common_weighted_inverse
    (comparison : MovingPatchSourceComparison) (correctedFirst correctedFinal : PeriodicC1HolderHalf)
    {weight inverseFactor : ℝ} (weightPositive : 0 < weight) (inverseNonnegative : 0 ≤ inverseFactor)
    (inverse : EulerNonuniqueness.General.weightedProjectionDistance
      diskPhysicalTransverseProjection diskNeutralCLM weight comparison.initial comparison.final ≤
      inverseFactor * EulerNonuniqueness.General.weightedProjectionDistance
        diskPhysicalTransverseProjection diskNeutralCLM weight correctedFirst correctedFinal) :
    comparison.spectralDifferenceBudget ≤
      inverseFactor * max 1 ((‖diskPhysicalTransverseProjection comparison.initial‖ +
        ‖diskPhysicalTransverseProjection comparison.final‖) / weight) *
      EulerNonuniqueness.General.weightedProjectionDistance
        diskPhysicalTransverseProjection diskNeutralCLM weight correctedFirst correctedFinal := by
  simpa only [spectralDifferenceBudget] using EulerNonuniqueness.General.weightedProjectionShapeBudget_le_of_weighted_inverse
    diskPhysicalTransverseProjection diskNeutralCLM comparison.initial comparison.final
    correctedFirst correctedFinal weightPositive inverseNonnegative inverse

end EulerNonuniqueness.Paper.MovingPatchSourceComparison
