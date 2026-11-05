import EulerNonuniqueness.Section3.CrossContourLipschitz

namespace EulerNonuniqueness.Paper

noncomputable section

def UniformlySeparatedContours (target source : PeriodicC1HolderHalf) : Prop :=
  ∃ lower : ℝ, 0 < lower ∧ ∀ sourceLabel targetLabel,
    lower ≤ ‖target.val.1 targetLabel - source.val.1 sourceLabel‖

def extendedCrossContourVelocity (target source : PeriodicC1HolderHalf) : PeriodicC1HolderHalf := by
  classical
  exact if separated : UniformlySeparatedContours target source then
    crossContourVelocityBanach target source separated.choose_spec.1 separated.choose_spec.2
  else 0

theorem extendedCrossContourVelocity_eq (target source : PeriodicC1HolderHalf) {lower : ℝ}
    (lower_pos : 0 < lower)
    (separated : ∀ sourceLabel targetLabel, lower ≤ ‖target.val.1 targetLabel - source.val.1 sourceLabel‖) :
    extendedCrossContourVelocity target source = crossContourVelocityBanach target source lower_pos separated := by
  have uniformly_separated : UniformlySeparatedContours target source := ⟨lower, lower_pos, separated⟩
  rw [extendedCrossContourVelocity, dif_pos uniformly_separated]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [crossContourVelocityBanach_value, crossContourVelocityBanach_value]

theorem extendedCrossContourVelocity_parameter_norm_bound
    (firstTarget firstSource secondTarget secondSource : PeriodicC1HolderHalf)
    {lower bound : ℝ} (lower_pos : 0 < lower)
    (first_separated : ∀ sourceLabel targetLabel,
      lower ≤ ‖firstTarget.val.1 targetLabel - firstSource.val.1 sourceLabel‖)
    (second_separated : ∀ sourceLabel targetLabel,
      lower ≤ ‖secondTarget.val.1 targetLabel - secondSource.val.1 sourceLabel‖)
    (first_target_bound : ‖firstTarget‖ ≤ bound) (first_source_bound : ‖firstSource‖ ≤ bound)
    (second_target_bound : ‖secondTarget‖ ≤ bound) (second_source_bound : ‖secondSource‖ ≤ bound) :
    ‖extendedCrossContourVelocity firstTarget firstSource - extendedCrossContourVelocity secondTarget secondSource‖ ≤
      (crossContourIntegrandLipschitzBound bound lower / 2) *
        (‖firstTarget - secondTarget‖ + ‖firstSource - secondSource‖) := by
  rw [extendedCrossContourVelocity_eq firstTarget firstSource lower_pos first_separated,
    extendedCrossContourVelocity_eq secondTarget secondSource lower_pos second_separated]
  exact crossContourVelocityBanach_parameter_norm_bound firstTarget firstSource secondTarget secondSource lower_pos
    first_separated second_separated first_target_bound first_source_bound second_target_bound second_source_bound

theorem crossContourIntegrandLipschitzBound_nonneg {bound lower : ℝ}
    (bound_nonneg : 0 ≤ bound) (lower_pos : 0 < lower) :
    0 ≤ crossContourIntegrandLipschitzBound bound lower := by
  have inverse_nonneg : 0 ≤ c1InverseUniformBound (2 * bound) lower :=
    (by positivity : 0 ≤ 1 / lower).trans (le_max_left _ _)
  unfold crossContourIntegrandLipschitzBound crossContourPhaseLipschitzBound crossContourPhaseBound
  positivity

end

end EulerNonuniqueness.Paper
