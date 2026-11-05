import EulerNonuniqueness.General.WeightedJensen

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness

theorem norm_integral_pow_le_integral_norm_pow {Domain Value : Type*}
    [MeasurableSpace Domain] [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {measure : Measure Domain} [IsProbabilityMeasure measure] {function : Domain → Value}
    (integrable : Integrable function measure) (power : ℕ)
    (momentIntegrable : Integrable (fun point => ‖function point‖ ^ power) measure) :
    ‖∫ point, function point ∂measure‖ ^ power ≤ ∫ point, ‖function point‖ ^ power ∂measure := by
  have jensen := (convexOn_pow power : ConvexOn ℝ (Ici 0) (fun value : ℝ => value ^ power)).map_integral_le
    (continuous_pow power).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall fun point => norm_nonneg (function point)) integrable.norm momentIntegrable
  calc
    _ ≤ (∫ point, ‖function point‖ ∂measure) ^ power := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact norm_integral_le_integral_norm function
    _ ≤ _ := jensen

end EulerNonuniqueness
