import Mathlib.Analysis.NormedSpace.OperatorNorm.Completeness
import Mathlib.Analysis.Complex.Basic

namespace EulerNonuniqueness.General

theorem completeSpace_complexOperator {Domain Target : Type*}
    [NormedAddCommGroup Domain] [NormedSpace ℂ Domain]
    [NormedAddCommGroup Target] [NormedSpace ℂ Target] [CompleteSpace Target] :
    CompleteSpace (Domain →L[ℂ] Target) := inferInstance

end EulerNonuniqueness.General
