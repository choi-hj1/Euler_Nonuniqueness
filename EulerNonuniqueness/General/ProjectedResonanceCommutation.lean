import EulerNonuniqueness.General.ProjectedQuadraticResonance
import EulerNonuniqueness.General.QuadraticCoordinateSeparation

namespace EulerNonuniqueness.General

open MeasureTheory

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

def projectedQuadraticOperator (projection : Space →L[ℝ] Space) : BilinearEnd Space →L[ℝ] BilinearEnd Space :=
  (bilinearPostcomposeOperator projection).comp
    ((bilinearFirstOperator projection).comp (bilinearSecondOperator projection))

theorem projectedQuadraticOperator_apply (projection : Space →L[ℝ] Space) (bilinear : BilinearEnd Space) :
    projectedQuadraticOperator projection bilinear = projectedQuadratic projection bilinear := by
  ext first second
  rfl

theorem quadraticConjugate_projectedQuadratic
    (group : ℝ → Space →L[ℝ] Space) (projection : Space →L[ℝ] Space)
    (commutes : ∀ time, projection.comp (group time) = (group time).comp projection)
    (bilinear : BilinearEnd Space) (time : ℝ) :
    quadraticConjugate group time (projectedQuadratic projection bilinear) =
      projectedQuadratic projection (quadraticConjugate group time bilinear) := by
  have pointwise (parameter : ℝ) (value : Space) : projection (group parameter value) = group parameter (projection value) :=
    congrArg (fun operator : Space →L[ℝ] Space => operator value) (commutes parameter)
  ext first second
  change group (-time) (projection (bilinear (projection (group time first)) (projection (group time second)))) =
    projection (group (-time) (bilinear (group time (projection first)) (group time (projection second))))
  rw [pointwise time first, pointwise time second, pointwise (-time)]

theorem quadraticResonance_projectedQuadratic
    (group : ℝ → Space →L[ℝ] Space) (generator projection : Space →L[ℝ] Space) (period : ℝ)
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second : ℝ, group (first + second) = (group first).comp (group second))
    (actualDerivative : ∀ time : ℝ, HasDerivAt group ((group time).comp generator) time)
    (commutes : ∀ time, projection.comp (group time) = (group time).comp projection)
    (bilinear : BilinearEnd Space) :
    quadraticResonance group period (projectedQuadratic projection bilinear) =
      projectedQuadratic projection (quadraticResonance group period bilinear) := by
  let operator := projectedQuadraticOperator projection
  have continuous : Continuous (fun time => quadraticConjugate group time bilinear) :=
    continuous_iff_continuousAt.mpr (fun time => HasDerivAt.continuousAt (F := BilinearEnd Space)
      (quadraticConjugate_hasDerivAt group generator atZero addition actualDerivative bilinear time))
  have integrable := continuous.intervalIntegrable (E := BilinearEnd Space) (μ := volume) 0 period
  rw [← projectedQuadraticOperator_apply projection (quadraticResonance group period bilinear)]
  change (1 / period : ℝ) • (∫ time in (0 : ℝ)..period,
      quadraticConjugate group time (projectedQuadratic projection bilinear)) =
    operator ((1 / period : ℝ) • ∫ time in (0 : ℝ)..period, quadraticConjugate group time bilinear)
  have integralCommutes : (∫ time in (0 : ℝ)..period, operator (quadraticConjugate group time bilinear)) =
      operator (∫ time in (0 : ℝ)..period, quadraticConjugate group time bilinear) := by
    with_reducible
      exact ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ)
        (E := BilinearEnd Space) (F := BilinearEnd Space) operator integrable
  rw [map_smul, ← integralCommutes]
  congr 1
  apply intervalIntegral.integral_congr
  intro time _
  dsimp only [operator]
  rw [projectedQuadraticOperator_apply projection (quadraticConjugate group time bilinear)]
  exact quadraticConjugate_projectedQuadratic group projection commutes bilinear time

theorem transverse_resonance_on_transverse_inputs_zero
    (group : ℝ → Space →L[ℝ] Space) (generator projection : Space →L[ℝ] Space) {halfPeriod : ℝ}
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second : ℝ, group (first + second) = (group first).comp (group second))
    (actualDerivative : ∀ time : ℝ, HasDerivAt group ((group time).comp generator) time)
    (commutes : ∀ time, projection.comp (group time) = (group time).comp projection)
    (idempotent : projection.comp projection = projection)
    (leftHalf : projection.comp (group halfPeriod) = -projection)
    (rightHalf : (group halfPeriod).comp projection = -projection) (bilinear : BilinearEnd Space)
    (first second : Space) :
    projection (quadraticResonance group (2 * halfPeriod) bilinear (projection first) (projection second)) = 0 := by
  have identity := quadraticResonance_projectedQuadratic group generator projection (2 * halfPeriod)
    atZero addition actualDerivative commutes bilinear
  rw [projectedQuadratic_resonance_zero group generator projection atZero addition actualDerivative
    idempotent leftHalf rightHalf bilinear] at identity
  have evaluated := congrArg (fun operator : BilinearEnd Space => operator first second) identity.symm
  exact evaluated

theorem projected_bilinear_neutral_defect_bound
    (projection : Space →L[ℝ] Space) (bilinear : BilinearEnd Space)
    (transverseZero : ∀ first second, projection (bilinear (projection first) (projection second)) = 0)
    (value : Space) :
    ‖projection (bilinear value value)‖ ≤
      ‖projection‖ * ‖bilinear‖ * (1 + ‖projection‖) * ‖value‖ * ‖value - projection value‖ := by
  have difference : projection (bilinear value value) =
      projection (bilinear value value - bilinear (projection value) (projection value)) := by
    rw [map_sub, transverseZero, sub_zero]
  rw [difference]
  calc
    _ ≤ ‖projection‖ * ‖bilinear value value - bilinear (projection value) (projection value)‖ := projection.le_opNorm _
    _ ≤ ‖projection‖ * (‖bilinear‖ * (‖value‖ + ‖projection value‖) * ‖value - projection value‖) :=
      mul_le_mul_of_nonneg_left (quadratic_diagonal_sub_norm_le bilinear value (projection value)) (norm_nonneg _)
    _ ≤ ‖projection‖ * (‖bilinear‖ * (‖value‖ + ‖projection‖ * ‖value‖) * ‖value - projection value‖) := by
      gcongr
      exact projection.le_opNorm value
    _ = _ := by ring

end

end EulerNonuniqueness.General
