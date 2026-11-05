import Mathlib.Analysis.Fourier.AddCircle

open MeasureTheory

namespace EulerNonuniqueness

noncomputable section

def periodicContinuousLift {period : ℝ} {function : ℝ → ℂ}
    (continuous : Continuous function) (periodic : Function.Periodic function period) :
    C(AddCircle period, ℂ) :=
  ⟨periodic.lift, continuous_quot_lift _ continuous⟩

theorem periodicContinuousLift_coe {period : ℝ} {function : ℝ → ℂ}
    (continuous : Continuous function) (periodic : Function.Periodic function period) (position : ℝ) :
    periodicContinuousLift continuous periodic (position : AddCircle period) = function position :=
  periodic.lift_coe position

theorem eq_of_periodic_fourierCoeff_eq {period : ℝ} [Fact (0 < period)]
    {first second : ℝ → ℂ} (firstContinuous : Continuous first) (secondContinuous : Continuous second)
    (firstPeriodic : Function.Periodic first period) (secondPeriodic : Function.Periodic second period)
    (coefficients : ∀ degree : ℤ,
      fourierCoeff (periodicContinuousLift firstContinuous firstPeriodic) degree =
        fourierCoeff (periodicContinuousLift secondContinuous secondPeriodic) degree) : first = second := by
  let firstLift := periodicContinuousLift firstContinuous firstPeriodic
  let secondLift := periodicContinuousLift secondContinuous secondPeriodic
  have quotientEquality :
      ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ firstLift =
        ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ secondLift := by
    apply fourierBasis.repr.injective
    ext degree
    rw [fourierBasis_repr, fourierBasis_repr, fourierCoeff_toLp, fourierCoeff_toLp]
    exact coefficients degree
  have liftEquality : firstLift = secondLift :=
    (ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle) quotientEquality
  funext position
  exact congrArg (fun function : C(AddCircle period, ℂ) => function (position : AddCircle period)) liftEquality

end

end EulerNonuniqueness
