import EulerNonuniqueness.Section3.LocalLipschitzCalculus
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Operator.Banach

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem inverse_operator_lipschitzNear_identity :
    LipschitzNear (Ring.inverse : (Space →L[ℝ] Space) → Space →L[ℝ] Space)
      (ContinuousLinearMap.id ℝ Space) := by
  change LipschitzNear (Ring.inverse : (Space →L[ℝ] Space) → Space →L[ℝ] Space)
    ((1 : (Space →L[ℝ] Space)ˣ) : Space →L[ℝ] Space)
  exact lipschitzNear_of_analyticAt (analyticAt_inverse (𝕜 := ℝ) (1 : (Space →L[ℝ] Space)ˣ))

end EulerNonuniqueness.General
