import EulerNonuniqueness.Section5.UniformSeedSmallness

noncomputable section

open Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_cascadeParameterPrerequisites (scales : Scales) (orbit : SeparatingOrbit)
    (alphaPositive : 0 < scales.alpha) (alphaBound : scales.alpha < 1)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 < scales.ratio)
    (normalized : IsNormalizedSeparatingOrbit orbit)
    {sectionTime threshold tolerance timingConstant : ℝ} (sectionTimePositive : 0 < sectionTime)
    (thresholdPositive : 0 < threshold) (thresholdBound : threshold < 1 / 8)
    (tolerancePositive : 0 < tolerance) (toleranceBound : tolerance < 1 / 8)
    (timingPositive : 0 < timingConstant) :
    ∀ᶠ frequency : ℝ in atTop, CascadeParameterPrerequisites {scales with frequency := frequency}
      orbit sectionTime threshold tolerance timingConstant := by
  have seedsSmall := scales.eventually_seed_lt_one ratioBound.le alphaPositive
  have delaysSmall := scales.eventually_actual_delay_total_lt
    (show 1 < scales.ratio by linarith) alphaBound sectionTime (show (0 : ℝ) < 1 / 4 by norm_num)
  filter_upwards [eventually_gt_atTop (0 : ℝ), seedsSmall, delaysSmall]
    with frequency frequencyPositive seedsSmall delaysSmall
  let changed : Scales := {scales with frequency := frequency}
  refine ⟨alphaPositive, alphaBound, amplitudePositive, ratioBound, frequencyPositive, normalized,
    sectionTimePositive, thresholdPositive, thresholdBound, tolerancePositive, toleranceBound,
    timingPositive, ?_, ?_, delaysSmall⟩
  · intro index _
    exact ⟨changed.seed_pos frequencyPositive (by linarith) index, seedsSmall index,
      changed.actual_delay_pos frequencyPositive (by linarith) sectionTimePositive index (seedsSmall index)⟩
  · exact changed.actual_delay_summable frequencyPositive (by linarith) alphaBound sectionTime

theorem Scales.exists_frequency_cascadeParameterPrerequisites (scales : Scales) (orbit : SeparatingOrbit)
    (alphaPositive : 0 < scales.alpha) (alphaBound : scales.alpha < 1)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 < scales.ratio)
    (normalized : IsNormalizedSeparatingOrbit orbit)
    {sectionTime threshold tolerance timingConstant : ℝ} (sectionTimePositive : 0 < sectionTime)
    (thresholdPositive : 0 < threshold) (thresholdBound : threshold < 1 / 8)
    (tolerancePositive : 0 < tolerance) (toleranceBound : tolerance < 1 / 8)
    (timingPositive : 0 < timingConstant) (minimumFrequency : ℝ) :
    ∃ frequency : ℝ, minimumFrequency ≤ frequency ∧
      CascadeParameterPrerequisites {scales with frequency := frequency}
        orbit sectionTime threshold tolerance timingConstant := by
  exact ((eventually_ge_atTop minimumFrequency).and
    (scales.eventually_cascadeParameterPrerequisites orbit alphaPositive alphaBound amplitudePositive ratioBound normalized
      sectionTimePositive thresholdPositive thresholdBound tolerancePositive toleranceBound timingPositive)).exists

end EulerNonuniqueness.Paper
