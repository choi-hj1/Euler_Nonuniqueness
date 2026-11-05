import EulerNonuniqueness.General.QuadraticHomologicalLipschitz
import Mathlib.Topology.Instances.RealVectorSpace

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

def quadraticHomologicalLinearMap
    (group : ℝ → Space →L[ℝ] Space) (generator : Space →L[ℝ] Space) {period bound : ℝ}
    (positive : 0 < period) (nonnegative : 0 ≤ bound)
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second : ℝ, group (first + second) = (group first).comp (group second))
    (actualDerivative : ∀ time : ℝ, HasDerivAt group ((group time).comp generator) time)
    (groupBound : ∀ time : ℝ, ∀ value : Space, ‖group time value‖ ≤ bound * ‖value‖) :
    BilinearEnd Space →L[ℝ] BilinearEnd Space := by
  let solution := quadraticHomologicalSolution group period
  have subtraction : ∀ first second, solution (first - second) = solution first - solution second :=
    quadraticHomologicalSolution_sub group generator period atZero addition actualDerivative
  have zero : solution 0 = 0 := by
    simpa only [sub_self] using subtraction 0 0
  let additive : BilinearEnd Space →+ BilinearEnd Space := {
    toFun := solution
    map_zero' := zero
    map_add' := fun first second => by
      have identity := subtraction (first + second) second
      rw [add_sub_cancel_right] at identity
      exact (eq_sub_iff_add_eq.mp identity).symm }
  have coefficient : 0 ≤ (period / 2) * bound ^ 3 :=
    mul_nonneg (by positivity) (pow_nonneg nonnegative _)
  have lipschitz : LipschitzWith ⟨(period / 2) * bound ^ 3, coefficient⟩ solution := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    simpa only [dist_eq_norm, NNReal.coe_mk] using
      quadraticHomologicalSolution_difference_norm_le group generator positive nonnegative
        atZero addition actualDerivative groupBound first second
  exact additive.toRealLinearMap lipschitz.continuous

theorem quadraticHomologicalLinearMap_apply
    (group : ℝ → Space →L[ℝ] Space) (generator : Space →L[ℝ] Space) {period bound : ℝ}
    (positive : 0 < period) (nonnegative : 0 ≤ bound)
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second : ℝ, group (first + second) = (group first).comp (group second))
    (actualDerivative : ∀ time : ℝ, HasDerivAt group ((group time).comp generator) time)
    (groupBound : ∀ time : ℝ, ∀ value : Space, ‖group time value‖ ≤ bound * ‖value‖)
    (bilinear : BilinearEnd Space) :
    quadraticHomologicalLinearMap group generator positive nonnegative atZero addition actualDerivative
      groupBound bilinear = quadraticHomologicalSolution group period bilinear := rfl

end

end EulerNonuniqueness.General
