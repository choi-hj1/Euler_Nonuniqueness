import EulerNonuniqueness.General.ProjectedAntipodalQuadratic

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

def projectedQuadratic (projection : Space →L[ℝ] Space) (bilinear : BilinearEnd Space) : BilinearEnd Space :=
  bilinearPostcompose projection (bilinear.bilinearComp projection projection)

theorem projectedQuadratic_input (projection : Space →L[ℝ] Space)
    (idempotent : projection.comp projection = projection) (bilinear : BilinearEnd Space) (first second : Space) :
    projectedQuadratic projection bilinear (projection first) (projection second) =
      projectedQuadratic projection bilinear first second := by
  have projected (value : Space) : projection (projection value) = projection value :=
    congrArg (fun operator : Space →L[ℝ] Space => operator value) idempotent
  change projection (bilinear (projection (projection first)) (projection (projection second))) =
    projection (bilinear (projection first) (projection second))
  rw [projected, projected]

theorem projectedQuadratic_output (projection : Space →L[ℝ] Space)
    (idempotent : projection.comp projection = projection) (bilinear : BilinearEnd Space) (first second : Space) :
    projection (projectedQuadratic projection bilinear first second) =
      projectedQuadratic projection bilinear first second := by
  exact congrArg (fun operator : Space →L[ℝ] Space => operator (bilinear (projection first) (projection second))) idempotent

theorem projectedQuadratic_resonance_zero
    (group : ℝ → Space →L[ℝ] Space) (generator projection : Space →L[ℝ] Space) {halfPeriod : ℝ}
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second : ℝ, group (first + second) = (group first).comp (group second))
    (actualDerivative : ∀ time : ℝ, HasDerivAt group ((group time).comp generator) time)
    (idempotent : projection.comp projection = projection)
    (leftHalf : projection.comp (group halfPeriod) = -projection)
    (rightHalf : (group halfPeriod).comp projection = -projection) (bilinear : BilinearEnd Space) :
    quadraticResonance group (2 * halfPeriod) (projectedQuadratic projection bilinear) = 0 :=
  quadraticResonance_eq_zero_of_projected_antipodal group generator projection atZero addition actualDerivative
    leftHalf rightHalf (projectedQuadratic projection bilinear)
    (projectedQuadratic_input projection idempotent bilinear) (projectedQuadratic_output projection idempotent bilinear)

end

end EulerNonuniqueness.General
