import EulerNonuniqueness.General.QuadraticCommutatorOperator
import EulerNonuniqueness.General.PeriodicLinearAveraging

namespace EulerNonuniqueness.General

noncomputable section

set_option maxHeartbeats 1000000

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

def quadraticResonance (group : ℝ → Space →L[ℝ] Space) (period : ℝ) (bilinear : BilinearEnd Space) :
    BilinearEnd Space := (1 / period : ℝ) • ∫ time in (0 : ℝ)..period, quadraticConjugate group time bilinear

def quadraticHomologicalSolution (group : ℝ → Space →L[ℝ] Space) (period : ℝ) (bilinear : BilinearEnd Space) :
    BilinearEnd Space := (1 / period : ℝ) • ∫ time in (0 : ℝ)..period, time • quadraticConjugate group time bilinear

theorem quadraticConjugate_zero (group : ℝ → Space →L[ℝ] Space)
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space) (bilinear : BilinearEnd Space) :
    quadraticConjugate group 0 bilinear = bilinear := by
  ext first second
  simp [quadraticConjugate, bilinearPostcompose, atZero]

theorem quadraticConjugate_at_period
    (group : ℝ → Space →L[ℝ] Space) (period : ℝ)
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second : ℝ, group (first + second) = (group first).comp (group second))
    (atPeriod : group period = ContinuousLinearMap.id ℝ Space) (bilinear : BilinearEnd Space) :
    quadraticConjugate group period bilinear = bilinear := by
  have atNegative : group (-period) = ContinuousLinearMap.id ℝ Space := by
    have identity := addition (-period) period
    simpa only [neg_add_cancel, atZero, atPeriod, ContinuousLinearMap.comp_id] using identity.symm
  ext first second
  simp [quadraticConjugate, bilinearPostcompose, atPeriod, atNegative]

theorem quadratic_homological_identity
    (group : ℝ → Space →L[ℝ] Space) (generator : Space →L[ℝ] Space) {period : ℝ}
    (periodPositive : 0 < period)
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second : ℝ, group (first + second) = (group first).comp (group second))
    (actualDerivative : ∀ time : ℝ, HasDerivAt group ((group time).comp generator) time)
    (atPeriod : group period = ContinuousLinearMap.id ℝ Space) (bilinear : BilinearEnd Space) :
    quadraticCommutator generator (quadraticHomologicalSolution group period bilinear) =
      bilinear - quadraticResonance group period bilinear := by
  have actual (time : ℝ) : HasDerivAt (fun current => quadraticConjugate group current bilinear)
      (quadraticCommutatorOperator generator (quadraticConjugate group time bilinear)) time := by
    simpa only [quadraticCommutatorOperator_apply] using
      quadraticConjugate_hasDerivAt group generator atZero addition actualDerivative bilinear time
  have endpoint : quadraticConjugate group period bilinear = quadraticConjugate group 0 bilinear := by
    rw [quadraticConjugate_zero group atZero, quadraticConjugate_at_period group period atZero addition atPeriod]
  have identity : quadraticCommutatorOperator generator
      ((1 / period : ℝ) • ∫ time in (0 : ℝ)..period, time • quadraticConjugate group time bilinear) =
      quadraticConjugate group 0 bilinear -
        (1 / period : ℝ) • ∫ time in (0 : ℝ)..period, quadraticConjugate group time bilinear := by
    with_reducible
      exact periodic_linear_weighted_average_identity (Value := BilinearEnd Space)
        (trajectory := fun time => quadraticConjugate group time bilinear)
        (period := period) (quadraticCommutatorOperator generator) periodPositive.ne' actual endpoint
  simpa only [quadraticConjugate_zero group atZero, quadraticCommutatorOperator_apply,
    quadraticHomologicalSolution, quadraticResonance] using identity

theorem quadratic_resonance_commutator_zero
    (group : ℝ → Space →L[ℝ] Space) (generator : Space →L[ℝ] Space) {period : ℝ}
    (atZero : group 0 = ContinuousLinearMap.id ℝ Space)
    (addition : ∀ first second : ℝ, group (first + second) = (group first).comp (group second))
    (actualDerivative : ∀ time : ℝ, HasDerivAt group ((group time).comp generator) time)
    (atPeriod : group period = ContinuousLinearMap.id ℝ Space) (bilinear : BilinearEnd Space) :
    quadraticCommutator generator (quadraticResonance group period bilinear) = 0 := by
  have actual (time : ℝ) : HasDerivAt (fun current => quadraticConjugate group current bilinear)
      (quadraticCommutatorOperator generator (quadraticConjugate group time bilinear)) time := by
    simpa only [quadraticCommutatorOperator_apply] using
      quadraticConjugate_hasDerivAt group generator atZero addition actualDerivative bilinear time
  have endpoint : quadraticConjugate group period bilinear = quadraticConjugate group 0 bilinear := by
    rw [quadraticConjugate_zero group atZero, quadraticConjugate_at_period group period atZero addition atPeriod]
  have identity : quadraticCommutatorOperator generator
      ((1 / period : ℝ) • ∫ time in (0 : ℝ)..period, quadraticConjugate group time bilinear) = 0 := by
    with_reducible
      exact periodic_linear_average_kernel (Value := BilinearEnd Space)
        (trajectory := fun time => quadraticConjugate group time bilinear)
        (period := period) (quadraticCommutatorOperator generator) actual endpoint
  simpa only [quadraticCommutatorOperator_apply, quadraticResonance] using identity

end

end EulerNonuniqueness.General
