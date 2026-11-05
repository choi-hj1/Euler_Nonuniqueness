import Mathlib.Analysis.NormedSpace.OperatorNorm.Completeness

namespace EulerNonuniqueness.General

theorem completeSpace_realOperator {Domain Target : Type*}
    [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target] [CompleteSpace Target] :
    CompleteSpace (Domain →L[ℝ] Target) := inferInstance

end EulerNonuniqueness.General
