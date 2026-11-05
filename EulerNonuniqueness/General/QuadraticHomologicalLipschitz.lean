import EulerNonuniqueness.General.PeriodicQuadraticBounds

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem quadraticConjugate_sub (group : ℝ → Space →L[ℝ] Space) (time : ℝ)
    (first second : BilinearEnd Space) :
    quadraticConjugate group time (first - second) =
      quadraticConjugate group time first - quadraticConjugate group time second := by
  apply ContinuousLinearMap.ext
  intro left
  apply ContinuousLinearMap.ext
  intro right
  change group (-time) (first (group time left) (group time right) - second (group time left) (group time right)) =
    group (-time) (first (group time left) (group time right)) -
      group (-time) (second (group time left) (group time right))
  exact map_sub _ _ _

theorem quadraticHomologicalSolution_sub
    (group : ℝ → Space →L[ℝ] Space) (generator : Space →L[ℝ] Space) (period : ℝ)
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second : ℝ, group (first + second) = (group first).comp (group second))
    (actualDerivative : ∀ time : ℝ, HasDerivAt group ((group time).comp generator) time)
    (first second : BilinearEnd Space) :
    quadraticHomologicalSolution group period (first - second) =
      quadraticHomologicalSolution group period first - quadraticHomologicalSolution group period second := by
  have continuous (bilinear : BilinearEnd Space) : Continuous (fun time => quadraticConjugate group time bilinear) :=
    continuous_iff_continuousAt.mpr (fun time => HasDerivAt.continuousAt (F := BilinearEnd Space)
      (quadraticConjugate_hasDerivAt group generator atZero addition actualDerivative bilinear time))
  unfold quadraticHomologicalSolution
  simp_rw [quadraticConjugate_sub, smul_sub]
  rw [intervalIntegral.integral_sub ((continuous_id.smul (continuous first)).intervalIntegrable 0 period)
    ((continuous_id.smul (continuous second)).intervalIntegrable 0 period), smul_sub]

theorem quadraticHomologicalSolution_difference_norm_le
    (group : ℝ → Space →L[ℝ] Space) (generator : Space →L[ℝ] Space) {period bound : ℝ}
    (positive : 0 < period) (nonnegative : 0 ≤ bound)
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second : ℝ, group (first + second) = (group first).comp (group second))
    (actualDerivative : ∀ time : ℝ, HasDerivAt group ((group time).comp generator) time)
    (groupBound : ∀ time : ℝ, ∀ value : Space, ‖group time value‖ ≤ bound * ‖value‖)
    (first second : BilinearEnd Space) :
    ‖quadraticHomologicalSolution group period first - quadraticHomologicalSolution group period second‖ ≤
      (period / 2) * bound ^ 3 * ‖first - second‖ := by
  rw [← quadraticHomologicalSolution_sub group generator period atZero addition actualDerivative]
  exact quadraticHomologicalSolution_norm_le group generator positive nonnegative atZero addition
    actualDerivative groupBound (first - second)

end

end EulerNonuniqueness.General
