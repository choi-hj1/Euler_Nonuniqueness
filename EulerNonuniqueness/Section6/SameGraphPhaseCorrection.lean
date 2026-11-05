import EulerNonuniqueness.Section6.ForcedAdjustedPhaseEquation

noncomputable section

namespace EulerNonuniqueness.Section6

theorem sameGraph_phaseCorrection_exists_uniform_stable_factor
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (graphZero : graph 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateZero : coordinate 0 = 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ContDiffAt ℝ 2 (phaseCorrection 1 graph) 0 ∧ phaseCorrection 1 graph 0 = 0 ∧
      HasDerivAt (phaseCorrection 1 graph) 0 0 ∧
      ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ frequency unstable stable : ℝ,
      |unstable| + |stable| < radius →
        |correctedPhaseError frequency (phaseCorrection 1 graph) (unstable, stable)| ≤
          bound * |frequency| * |stable - graph unstable| * (|coordinate unstable| + |stable - graph unstable|) := by
  have regular := phaseCorrection_regular 1 (by norm_num) graphAnalytic graphZero graphDerivative
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    phaseCorrection_stable_factor 1 (by norm_num) graphAnalytic graphZero graphDerivative coordinateZero coordinateDerivative
  refine ⟨regular.1, regular.2.1, regular.2.2.1, bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro frequency unstable stable small
  rw [correctedPhaseError_frequency_mul, abs_mul]
  have actual := mul_le_mul_of_nonneg_left (estimate unstable stable small) (abs_nonneg frequency)
  convert actual using 1 <;> ring

end EulerNonuniqueness.Section6
