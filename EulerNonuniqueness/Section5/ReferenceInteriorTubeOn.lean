import EulerNonuniqueness.Section5.ReferenceInteriorTube

open Set

namespace EulerNonuniqueness.Section5

theorem reference_interior_tube_of_actual_equations_on_Icc
    {rate unstable stable unstableForcing stableForcing : ℝ → ℝ}
    {decay horizon radius forcingBound quadratic : ℝ}
    (decayPositive : 0 < decay) (horizonNonnegative : 0 ≤ horizon)
    (radiusPositive : 0 < radius) (forcingNonnegative : 0 ≤ forcingBound)
    (quadraticNonnegative : 0 ≤ quadratic)
    (small : 16 * quadratic * radius ≤ decay)
    (rateContinuous : ContinuousOn rate (Icc 0 horizon))
    (unstableContinuous : ContinuousOn unstable (Icc 0 horizon))
    (stableContinuous : ContinuousOn stable (Icc 0 horizon))
    (unstableForcingContinuous : ContinuousOn unstableForcing (Icc 0 horizon))
    (stableForcingContinuous : ContinuousOn stableForcing (Icc 0 horizon))
    (rateLower : ∀ current ∈ Icc 0 horizon, decay ≤ rate current)
    (unstableEquation : ∀ current ∈ Icc 0 horizon,
      HasDerivAt unstable (rate current * unstable current + unstableForcing current) current)
    (stableEquation : ∀ current ∈ Icc 0 horizon,
      HasDerivAt stable (-rate current * stable current + stableForcing current) current)
    (stableInitial : stable 0 = 0)
    (bootstrap : ∀ current ∈ Icc 0 horizon, |unstable current| ≤ radius ∧ |stable current| ≤ radius)
    (forcingEstimate : ∀ current ∈ Icc 0 horizon,
      |unstableForcing current| + |stableForcing current| ≤
        quadratic * (|unstable current| + |stable current|) ^ 2 + forcingBound) :
    ∀ time ∈ Icc 0 horizon, |unstable time| + |stable time| ≤
      2 * (2 * forcingBound / decay + radius * Real.exp (-(decay / 2) * (horizon - time))) := by
  let extended : ℝ → ℝ := fun time => rate (projIcc 0 horizon horizonNonnegative time)
  have extendedContinuous : Continuous extended :=
    (continuousOn_iff_continuous_restrict.mp rateContinuous).comp continuous_projIcc
  have agrees (time : ℝ) (inside : time ∈ Icc 0 horizon) : extended time = rate time := by
    simp only [extended, projIcc_of_mem horizonNonnegative inside]
  apply reference_interior_tube_of_actual_equations
    (rate := extended) decayPositive horizonNonnegative radiusPositive forcingNonnegative
    quadraticNonnegative small extendedContinuous unstableContinuous stableContinuous
    unstableForcingContinuous stableForcingContinuous
  · intro current inside
    rw [agrees current inside]
    exact rateLower current inside
  · intro current inside
    rw [agrees current inside]
    exact unstableEquation current inside
  · intro current inside
    rw [agrees current inside]
    exact stableEquation current inside
  · exact stableInitial
  · exact bootstrap
  · exact forcingEstimate

end EulerNonuniqueness.Section5
