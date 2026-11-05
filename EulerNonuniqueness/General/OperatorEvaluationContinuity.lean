import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

namespace EulerNonuniqueness.General

theorem continuousAt_operator_evaluation {Domain Space Target : Type*}
    [TopologicalSpace Domain] [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    {operators : Domain → Space →L[ℝ] Target} {curve : Domain → Space} {point : Domain}
    (operatorContinuous : ContinuousAt operators point) (curveContinuous : ContinuousAt curve point) :
    ContinuousAt (fun current => operators current (curve current)) point :=
  (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Space) (F := Target)).continuous.continuousAt.comp
    (operatorContinuous.prodMk curveContinuous)

end EulerNonuniqueness.General
