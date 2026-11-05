import EulerNonuniqueness.General.PeriodicQuadraticHomological
import EulerNonuniqueness.General.PeriodicAverageBounds

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem quadraticResonance_norm_le
    (group : ℝ → Space →L[ℝ] Space) (generator : Space →L[ℝ] Space) {period bound : ℝ}
    (periodPositive : 0 < period) (boundNonnegative : 0 ≤ bound)
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second : ℝ, group (first + second) = (group first).comp (group second))
    (actualDerivative : ∀ time : ℝ, HasDerivAt group ((group time).comp generator) time)
    (groupBound : ∀ time : ℝ, ∀ value : Space, ‖group time value‖ ≤ bound * ‖value‖)
    (bilinear : BilinearEnd Space) :
    ‖quadraticResonance group period bilinear‖ ≤ bound ^ 3 * ‖bilinear‖ := by
  have continuous : Continuous (fun time => quadraticConjugate group time bilinear) :=
    continuous_iff_continuousAt.mpr (fun time => HasDerivAt.continuousAt (F := BilinearEnd Space)
      (quadraticConjugate_hasDerivAt group generator atZero addition actualDerivative bilinear time))
  unfold quadraticResonance
  with_reducible
    exact periodic_average_norm_le (Value := BilinearEnd Space)
      (trajectory := fun time => quadraticConjugate group time bilinear) periodPositive continuous
      (fun time _ => quadraticConjugate_norm_le group boundNonnegative groupBound time bilinear)

theorem quadraticHomologicalSolution_norm_le
    (group : ℝ → Space →L[ℝ] Space) (generator : Space →L[ℝ] Space) {period bound : ℝ}
    (periodPositive : 0 < period) (boundNonnegative : 0 ≤ bound)
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second : ℝ, group (first + second) = (group first).comp (group second))
    (actualDerivative : ∀ time : ℝ, HasDerivAt group ((group time).comp generator) time)
    (groupBound : ∀ time : ℝ, ∀ value : Space, ‖group time value‖ ≤ bound * ‖value‖)
    (bilinear : BilinearEnd Space) :
    ‖quadraticHomologicalSolution group period bilinear‖ ≤ (period / 2) * bound ^ 3 * ‖bilinear‖ := by
  have continuous : Continuous (fun time => quadraticConjugate group time bilinear) :=
    continuous_iff_continuousAt.mpr (fun time => HasDerivAt.continuousAt (F := BilinearEnd Space)
      (quadraticConjugate_hasDerivAt group generator atZero addition actualDerivative bilinear time))
  have estimate : ‖quadraticHomologicalSolution group period bilinear‖ ≤ (period / 2) * (bound ^ 3 * ‖bilinear‖) := by
    unfold quadraticHomologicalSolution
    with_reducible
      exact periodic_weighted_average_norm_le (Value := BilinearEnd Space)
        (trajectory := fun time => quadraticConjugate group time bilinear) periodPositive continuous
        (fun time _ => quadraticConjugate_norm_le group boundNonnegative groupBound time bilinear)
  simpa only [mul_assoc] using estimate

end

end EulerNonuniqueness.General
