import EulerNonuniqueness.Section5.CascadeExtentFrequencyBudget

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_cascade_pair_strain_budget (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {factor : ℝ} (factorPositive : 0 < factor) :
    ∀ᶠ frequency : ℝ in atTop,
      (2 / Real.pi) * (24 / factor) ^ 2 * ({scales with frequency := frequency}).strain ≤ 1 / 64 ∧
      (144 / (Real.pi * factor)) * ({scales with frequency := frequency}).strain ≤ 1 / 32 := by
  have firstPositive : 0 < (2 / Real.pi) * (24 / factor) ^ 2 := by positivity
  have secondPositive : 0 < 144 / (Real.pi * factor) := by positivity
  let tolerance := min ((1 / 64 : ℝ) / ((2 / Real.pi) * (24 / factor) ^ 2))
    ((1 / 32 : ℝ) / (144 / (Real.pi * factor)))
  have tolerancePositive : 0 < tolerance := by dsimp [tolerance]; positivity
  filter_upwards [(scales.strain_tendsto_zero ratioBound alphaPositive).eventually
    (eventually_lt_nhds tolerancePositive)] with frequency small
  have first := small.le.trans (min_le_left _ _)
  have second := small.le.trans (min_le_right _ _)
  have firstBound := (le_div_iff₀ firstPositive).mp first
  have secondBound := (le_div_iff₀ secondPositive).mp second
  constructor <;> linarith

end EulerNonuniqueness.Paper
