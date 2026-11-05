import EulerNonuniqueness.General.QuadraticHomologicalLipschitz
import EulerNonuniqueness.General.ProjectedQuadraticResonance
import EulerNonuniqueness.General.BilinearFiberNormBounds

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

local instance projectedHomologicalOperatorGroup : NormedAddCommGroup (Space →L[ℝ] Space) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Space) (F := Space)
    (σ₁₂ := RingHom.id ℝ)
local instance projectedHomologicalBilinearGroup : NormedAddCommGroup (BilinearEnd Space) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := Space) (F := Space →L[ℝ] Space) (σ₁₂ := RingHom.id ℝ)

theorem projectedQuadratic_sub (projection : Space →L[ℝ] Space) (first second : BilinearEnd Space) :
    projectedQuadratic projection (first - second) =
      projectedQuadratic projection first - projectedQuadratic projection second := by
  ext left right
  exact map_sub projection _ _

theorem projectedQuadratic_difference_norm_le (projection : Space →L[ℝ] Space)
    (first second : BilinearEnd Space) :
    ‖projectedQuadratic projection first - projectedQuadratic projection second‖ ≤
      ‖projection‖ ^ 3 * ‖first - second‖ := by
  rw [← projectedQuadratic_sub]
  have estimate := norm_bilinear_fiber_conjugate_le projection projection (first - second)
  convert estimate using 1 <;> ring

variable [CompleteSpace Space]

theorem projectedQuadraticHomological_difference_norm_le
    (group : ℝ → Space →L[ℝ] Space) (generator projection : Space →L[ℝ] Space) {period bound : ℝ}
    (positive : 0 < period) (nonnegative : 0 ≤ bound)
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second : ℝ, group (first + second) = (group first).comp (group second))
    (actualDerivative : ∀ time : ℝ, HasDerivAt group ((group time).comp generator) time)
    (groupBound : ∀ time : ℝ, ∀ value : Space, ‖group time value‖ ≤ bound * ‖value‖)
    (first second : BilinearEnd Space) :
    ‖quadraticHomologicalSolution group period (projectedQuadratic projection first) -
        quadraticHomologicalSolution group period (projectedQuadratic projection second)‖ ≤
      ((period / 2) * bound ^ 3 * ‖projection‖ ^ 3) * ‖first - second‖ := by
  apply (quadraticHomologicalSolution_difference_norm_le group generator positive nonnegative atZero addition
    actualDerivative groupBound _ _).trans
  calc
    _ ≤ (period / 2) * bound ^ 3 * (‖projection‖ ^ 3 * ‖first - second‖) := by
      gcongr
      exact projectedQuadratic_difference_norm_le projection first second
    _ = _ := by ring

theorem lipschitzOnWith_projectedQuadraticHomological
    {Parameter : Type*} [PseudoMetricSpace Parameter]
    (group : ℝ → Space →L[ℝ] Space) (generator projection : Space →L[ℝ] Space) {period bound : ℝ}
    (positive : 0 < period) (nonnegative : 0 ≤ bound)
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second : ℝ, group (first + second) = (group first).comp (group second))
    (actualDerivative : ∀ time : ℝ, HasDerivAt group ((group time).comp generator) time)
    (groupBound : ∀ time : ℝ, ∀ value : Space, ‖group time value‖ ≤ bound * ‖value‖)
    {coefficients : Parameter → BilinearEnd Space} {domain : Set Parameter} {constant : NNReal}
    (lipschitz : LipschitzOnWith constant coefficients domain) :
    LipschitzOnWith (⟨(period / 2) * bound ^ 3 * ‖projection‖ ^ 3, by positivity⟩ * constant)
      (fun parameter => quadraticHomologicalSolution group period (projectedQuadratic projection (coefficients parameter))) domain := by
  apply LipschitzOnWith.of_dist_le_mul
  intro first firstMember second secondMember
  have distanceIdentity :
      dist (quadraticHomologicalSolution group period (projectedQuadratic projection (coefficients first)))
        (quadraticHomologicalSolution group period (projectedQuadratic projection (coefficients second))) =
      ‖quadraticHomologicalSolution group period (projectedQuadratic projection (coefficients first)) -
        quadraticHomologicalSolution group period (projectedQuadratic projection (coefficients second))‖ :=
    dist_eq_norm _ _
  rw [distanceIdentity]
  apply (projectedQuadraticHomological_difference_norm_le group generator projection positive nonnegative atZero
    addition actualDerivative groupBound (coefficients first) (coefficients second)).trans
  have difference : ‖coefficients first - coefficients second‖ ≤ (constant : ℝ) * dist first second := by
    simpa only [dist_eq_norm] using lipschitz.dist_le_mul first firstMember second secondMember
  calc
    _ ≤ ((period / 2) * bound ^ 3 * ‖projection‖ ^ 3) * ((constant : ℝ) * dist first second) := by
      gcongr
    _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_mk]; ring

end

end EulerNonuniqueness.General
