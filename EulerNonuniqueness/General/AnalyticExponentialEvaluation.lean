import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Algebra.Exponential

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem analyticAt_exponential_generator_evaluation
    (generator : Space →L[ℝ] Space →L[ℝ] Space) (base point : Space) :
    AnalyticAt ℝ (fun current => NormedSpace.exp ℝ (generator current) base) point := by
  have operator : AnalyticAt ℝ (fun current => NormedSpace.exp ℝ (generator current)) point :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) (generator point)).comp (f := fun current => generator current)
      (generator.analyticAt point)
  exact ((ContinuousLinearMap.apply ℝ Space base).analyticAt (NormedSpace.exp ℝ (generator point))).comp
    (f := fun current => NormedSpace.exp ℝ (generator current)) operator

end

end EulerNonuniqueness.General
