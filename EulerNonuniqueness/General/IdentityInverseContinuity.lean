import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Ring.Units

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem continuousAt_inverse_family_of_identity
    (operator : Space → Space →L[ℝ] Space)
    (continuous : ContinuousAt operator (0 : Space))
    (identity : operator 0 = ContinuousLinearMap.id ℝ Space) :
    ContinuousAt (fun value => Ring.inverse (operator value)) (0 : Space) := by
  have inverseContinuous : ContinuousAt Ring.inverse (operator 0) := by
    rw [identity]
    exact NormedRing.inverse_continuousAt (1 : (Space →L[ℝ] Space)ˣ)
  exact inverseContinuous.comp continuous

theorem ring_inverse_continuousLinearEquiv (coordinates : Space ≃L[ℝ] Space) :
    Ring.inverse coordinates.toContinuousLinearMap = coordinates.symm.toContinuousLinearMap := by
  rw [ContinuousLinearMap.ringInverse_equiv, ContinuousLinearMap.inverse_equiv]

end

end EulerNonuniqueness.General
