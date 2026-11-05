import EulerNonuniqueness.Section5.ReferenceInteriorTubeOn
import EulerNonuniqueness.General.ClosedIntervalODEExtension

open Set

namespace EulerNonuniqueness.Section5

theorem reference_interior_tube_of_interior_equations
    {rate unstable stable unstableForcing stableForcing : ℝ → ℝ}
    {decay horizon radius forcingBound quadratic : ℝ}
    (decayPositive : 0 < decay) (horizonNonnegative : 0 ≤ horizon)
    (radiusPositive : 0 < radius) (forcingNonnegative : 0 ≤ forcingBound)
    (quadraticNonnegative : 0 ≤ quadratic) (small : 16 * quadratic * radius ≤ decay)
    (rateContinuous : ContinuousOn rate (Icc 0 horizon))
    (unstableContinuous : ContinuousOn unstable (Icc 0 horizon))
    (stableContinuous : ContinuousOn stable (Icc 0 horizon))
    (unstableForcingContinuous : ContinuousOn unstableForcing (Icc 0 horizon))
    (stableForcingContinuous : ContinuousOn stableForcing (Icc 0 horizon))
    (rateLower : ∀ current ∈ Icc 0 horizon, decay ≤ rate current)
    (unstableEquation : ∀ current ∈ Ioo 0 horizon,
      HasDerivAt unstable (rate current * unstable current + unstableForcing current) current)
    (stableEquation : ∀ current ∈ Ioo 0 horizon,
      HasDerivAt stable (-rate current * stable current + stableForcing current) current)
    (stableInitial : stable 0 = 0)
    (bootstrap : ∀ current ∈ Icc 0 horizon, |unstable current| ≤ radius ∧ |stable current| ≤ radius)
    (forcingEstimate : ∀ current ∈ Icc 0 horizon,
      |unstableForcing current| + |stableForcing current| ≤
        quadratic * (|unstable current| + |stable current|) ^ 2 + forcingBound) :
    ∀ time ∈ Icc 0 horizon, |unstable time| + |stable time| ≤
      2 * (2 * forcingBound / decay + radius * Real.exp (-(decay / 2) * (horizon - time))) := by
  obtain ⟨extendedUnstable, continuousUnstable, agreesUnstable, equationUnstable⟩ :=
    General.exists_closedInterval_ode_extension horizonNonnegative unstableContinuous
      ((rateContinuous.mul unstableContinuous).add unstableForcingContinuous) unstableEquation
  obtain ⟨extendedStable, continuousStable, agreesStable, equationStable⟩ :=
    General.exists_closedInterval_ode_extension horizonNonnegative stableContinuous
      (((rateContinuous.neg).mul stableContinuous).add stableForcingContinuous) stableEquation
  have tube := reference_interior_tube_of_actual_equations_on_Icc
    (unstable := extendedUnstable) (stable := extendedStable)
    decayPositive horizonNonnegative radiusPositive forcingNonnegative quadraticNonnegative small
    rateContinuous continuousUnstable.continuousOn continuousStable.continuousOn
    unstableForcingContinuous stableForcingContinuous rateLower
    (fun time inside => by simpa only [agreesUnstable inside] using equationUnstable time inside)
    (fun time inside => by simpa only [agreesStable inside] using equationStable time inside)
    (by rw [agreesStable ⟨le_rfl, horizonNonnegative⟩, stableInitial])
    (fun time inside => by simpa only [agreesUnstable inside, agreesStable inside] using bootstrap time inside)
    (fun time inside => by simpa only [agreesUnstable inside, agreesStable inside] using forcingEstimate time inside)
  intro time inside
  simpa only [agreesUnstable inside, agreesStable inside] using tube time inside

end EulerNonuniqueness.Section5
