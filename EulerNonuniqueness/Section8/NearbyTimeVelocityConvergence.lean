import EulerNonuniqueness.Section8.InitialVelocity
import EulerNonuniqueness.Section8.NearbyTimeLimits

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem LocalCompactnessHypotheses.tendsto_velocity_sub_at_nearby_times
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonPositive : 0 < horizon) (indices : ℕ → ℕ)
    (firstTimes secondTimes : ℕ → Icc (0 : ℝ) horizon)
    (nearby : Tendsto (fun index => (secondTimes index : ℝ) - firstTimes index) atTop (𝓝 0)) :
    Tendsto (fun index => eLpNorm
      (biotSavart (sequence (indices index) (firstTimes index)) -
        biotSavart (sequence (indices index) (secondTimes index))) 2 volume) atTop (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro sampling samplingTends
  obtain ⟨limit, datum, extraction, increasing, firstConverges, secondConverges⟩ :=
    hypotheses.exists_common_velocity_limit_at_nearby_times horizonPositive
      (indices ∘ sampling) (firstTimes ∘ sampling) (secondTimes ∘ sampling)
      (nearby.comp samplingTends)
  refine ⟨extraction, ?_⟩
  have limitMember := datum.biotSavart_memLp_two
  have estimate (index : ℕ) : eLpNorm
      (biotSavart (sequence (indices (sampling (extraction index))) (firstTimes (sampling (extraction index)))) -
        biotSavart (sequence (indices (sampling (extraction index))) (secondTimes (sampling (extraction index)))))
      2 volume ≤
      eLpNorm (biotSavart (sequence (indices (sampling (extraction index)))
        (firstTimes (sampling (extraction index)))) - biotSavart limit) 2 volume +
      eLpNorm (biotSavart (sequence (indices (sampling (extraction index)))
        (secondTimes (sampling (extraction index)))) - biotSavart limit) 2 volume := by
    have firstMember := hypotheses.biotSavart_memLp_two (indices (sampling (extraction index)))
      (firstTimes (sampling (extraction index))).property
    have secondMember := hypotheses.biotSavart_memLp_two (indices (sampling (extraction index)))
      (secondTimes (sampling (extraction index))).property
    have inequality := eLpNorm_sub_le (firstMember.sub limitMember).aestronglyMeasurable
      (secondMember.sub limitMember).aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    simpa only [sub_sub_sub_cancel_right] using inequality
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun index =>
      eLpNorm (biotSavart (sequence (indices (sampling (extraction index)))
        (firstTimes (sampling (extraction index)))) - biotSavart limit) 2 volume +
      eLpNorm (biotSavart (sequence (indices (sampling (extraction index)))
        (secondTimes (sampling (extraction index)))) - biotSavart limit) 2 volume) atTop (𝓝 0) by
      simpa only [Function.comp_def, add_zero] using firstConverges.add secondConverges)
    (fun _ => zero_le _) estimate

end EulerNonuniqueness
