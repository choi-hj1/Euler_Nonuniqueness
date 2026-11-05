import EulerNonuniqueness.Section3.HolderInverseAnalytic
import EulerNonuniqueness.Section3.ContourQuotientDerivative

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance quotientAnalyticHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance quotientAnalyticC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

theorem analyticAt_extendedContourTangentQuotient (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    AnalyticAt ℝ extendedContourTangentQuotient data := by
  have inverse : AnalyticAt ℝ extendedHolderInverse data.val.2 :=
    analyticAt_extendedHolderInverse data.val.2 (sub_pos.mpr (small.trans_le (min_le_left _ _)))
      (PeriodicC1HolderHalf.tangent_lower_bound data)
  have tangent : AnalyticAt ℝ (fun current : PeriodicC1HolderHalf => current.val.2) data :=
    c1TangentHolderRealCLM.analyticAt data
  have conjugate : AnalyticAt ℝ (fun current : PeriodicC1HolderHalf => holderConjugate current.val.2) data :=
    (contourHolderConjugateRealCLM.comp c1TangentHolderRealCLM).analyticAt data
  have inverse_composed : AnalyticAt ℝ (fun current : PeriodicC1HolderHalf =>
      extendedHolderInverse current.val.2) data :=
    inverse.comp (f := fun current : PeriodicC1HolderHalf => current.val.2) tangent
  exact (holderProductRealCLM.analyticAt_bilinear
    (holderConjugate data.val.2, extendedHolderInverse data.val.2)).comp₂
      (f := fun current : PeriodicC1HolderHalf => holderConjugate current.val.2)
      (g := fun current : PeriodicC1HolderHalf => extendedHolderInverse current.val.2)
      conjugate inverse_composed

end

end EulerNonuniqueness.Paper
