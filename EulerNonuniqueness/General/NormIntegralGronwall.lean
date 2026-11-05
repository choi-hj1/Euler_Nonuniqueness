import EulerNonuniqueness.General.IntegralGronwall

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness

theorem norm_integral_gronwall {space : Type*} [NormedAddCommGroup space] [NormedSpace ℝ space]
    {trajectory derivative : ℝ → space} {forcing : ℝ → ℝ} {rate horizon : ℝ}
    (trajectoryContinuous : Continuous trajectory) (forcingContinuous : Continuous forcing)
    (rateNonnegative : 0 ≤ rate) (horizonNonnegative : 0 ≤ horizon)
    (hasDerivative : ∀ time ∈ Ico 0 horizon,
      HasDerivWithinAt trajectory (derivative time) (Ici time) time)
    (bound : ∀ time ∈ Ico 0 horizon,
      ‖derivative time‖ ≤ rate * ‖trajectory time‖ + forcing time) :
    ∀ time ∈ Icc 0 horizon, ‖trajectory time‖ ≤ Real.exp (rate * time) *
      (‖trajectory 0‖ + ∫ current in (0 : ℝ)..time, Real.exp (-rate * current) * forcing current) := by
  let envelope := fun time => ‖trajectory 0‖ + ∫ current in (0 : ℝ)..time,
    forcing current + rate * ‖trajectory current‖
  have integrandContinuous : Continuous (fun time => forcing time + rate * ‖trajectory time‖) :=
    forcingContinuous.add (continuous_const.mul trajectoryContinuous.norm)
  have envelopeDerivative (time : ℝ) :
      HasDerivAt envelope (forcing time + rate * ‖trajectory time‖) time :=
    (intervalIntegral.integral_hasDerivAt_right (integrandContinuous.intervalIntegrable 0 time)
      integrandContinuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      integrandContinuous.continuousAt).const_add _
  have initial : ‖trajectory 0‖ ≤ envelope 0 := by simp [envelope]
  have inequality := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    trajectoryContinuous.continuousOn hasDerivative initial envelopeDerivative
    (fun time member => (bound time member).trans_eq (add_comm _ _))
  exact integral_gronwall_with_forcing trajectoryContinuous.norm forcingContinuous rateNonnegative
    horizonNonnegative (fun time member => inequality member)

end EulerNonuniqueness
