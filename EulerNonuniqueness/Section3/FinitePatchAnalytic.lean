import EulerNonuniqueness.Section3.FinitePatchContinuity
import EulerNonuniqueness.Section8.MomentEulerLimit
import EulerNonuniqueness.Section8.ExpandingEulerSequence
import EulerNonuniqueness.Section8.TransportAnalyticDecay

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.datum {count : ℕ} {scales : Scales}
    {motion : PatchMotion count} {horizon time : ℝ} (evolution : FinitePatchEvolution scales motion horizon)
    (inside : time ∈ Icc 0 horizon) (amplitudePositive : 0 < scales.amplitude)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio) :
    InitialDatum (patchVorticity scales motion time) := by
  have properties := evolution.2.2.2.1 time inside
  exact ⟨patchVorticity_hasCompactSupport scales motion time (fun index patch => (properties index patch).2.1),
    fun exponent _ => patchVorticity_memLp scales motion time (fun index patch => (properties index patch).1)
      (fun index patch => (properties index patch).2.1) _,
    patchVorticity_integral_zero scales motion time (fun index patch => (properties index patch).1)
      (fun index patch => (properties index patch).2.1) (fun index patch => (properties index patch).2.2.1)
      amplitudePositive frequencyPositive ratioPositive⟩

theorem FinitePatchEvolution.uniform_eLpNorm_bound {count : ℕ} {scales : Scales}
    {motion : PatchMotion count} {horizon : ℝ} (evolution : FinitePatchEvolution scales motion horizon)
    (amplitudePositive : 0 < scales.amplitude) {exponent : ℝ} (exponentBound : 1 ≤ exponent) :
    ∃ bound : ℝ≥0∞, bound < (⊤ : ℝ≥0∞) ∧ ∀ time ∈ Icc 0 horizon,
      eLpNorm (patchVorticity scales motion time) (ENNReal.ofReal exponent) volume ≤ bound := by
  let bound := 4 * ∑ index ∈ Finset.range count, scales.amplitude * scales.omega (index + 1) ^ 4 *
    (Real.pi * scales.radius (index + 1) ^ 2) ^ (1 / exponent)
  refine ⟨ENNReal.ofReal bound, ENNReal.ofReal_lt_top, ?_⟩
  intro time inside
  have properties := evolution.2.2.2.1 time inside
  have member := patchVorticity_memLp scales motion time (fun index patch => (properties index patch).1)
    (fun index patch => (properties index patch).2.1) (ENNReal.ofReal exponent)
  rw [← ENNReal.ofReal_toReal member.eLpNorm_lt_top.ne]
  exact ENNReal.ofReal_le_ofReal (patchVorticity_eLpNorm_toReal_le_sum scales motion time
    (fun index patch => (properties index patch).1) (fun index patch => (properties index patch).2.1)
    (fun index patch => (properties index patch).2.2.1) amplitudePositive exponentBound)

theorem FinitePatchEvolution.transportAnalyticHypotheses
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (supported : ∃ radius : ℝ, 0 < radius ∧ ∀ time ∈ Icc 0 horizon,
      Function.support (patchVorticity scales motion time) ⊆ Metric.closedBall 0 radius) :
    TransportAnalyticHypotheses horizon (patchVorticity scales motion 0) (patchVorticity scales motion) := by
  refine ⟨evolution.1, ?_, supported, ?_, fun _ bound => evolution.uniform_eLpNorm_bound amplitudePositive bound, ?_⟩
  · apply ContinuousInLpOn.weakL2ContinuousOn
    simpa using evolution.continuousInLp_vorticity (exponent := 2) (by norm_num)
  · intro exponent exponentBound time inside
    exact (evolution.datum inside amplitudePositive frequencyPositive ratioPositive).2.1 exponent exponentBound
  · intro time inside
    exact (evolution.datum inside amplitudePositive frequencyPositive ratioPositive).2.2

theorem FinitePatchEvolution.isEulerSolutionOn
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (positive : 0 < horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (supported : ∃ radius : ℝ, 0 < radius ∧ ∀ time ∈ Icc 0 horizon,
      Function.support (patchVorticity scales motion time) ⊆ Metric.closedBall 0 radius) :
    IsEulerSolutionOn horizon (patchVorticity scales motion 0) (patchVorticity scales motion) := by
  have analytic := evolution.transportAnalyticHypotheses amplitudePositive frequencyPositive ratioPositive supported
  exact analytic.isEulerSolutionOn positive analytic.continuousInLp_biotSavart

end EulerNonuniqueness.Paper
