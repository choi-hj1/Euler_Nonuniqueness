import EulerNonuniqueness.Section1.UniformInitialScaleSmallness
import EulerNonuniqueness.Section1.IndividualPatchInteractionWeight

noncomputable section

open Filter

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_radius_interaction_small (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {tolerance : ℝ} (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ receiver source : ℕ,
      let changed : Scales := {scales with frequency := frequency}
      changed.radius receiver ≤ tolerance * changed.individualInteractionDistance receiver source ∧
      changed.radius source ≤ tolerance * changed.individualInteractionDistance receiver source := by
  filter_upwards [scales.eventually_radius_lt_length amplitudePositive
      (show 1 ≤ scales.ratio by linarith) (show 0 < tolerance / 100 by positivity),
    scales.eventually_length_lt_location ratioBound alphaPositive (show (0 : ℝ) < 1 by norm_num)]
    with frequency radii lengths receiver source
  let changed : Scales := {scales with frequency := frequency}
  have radiusReceiver := (radii receiver).le
  have radiusSource := (radii source).le
  change changed.radius receiver ≤ _ at radiusReceiver
  change changed.radius source ≤ _ at radiusSource
  by_cases same : source = receiver
  · subst source
    simp only [Scales.individualInteractionDistance, if_pos rfl, if_true]
    constructor <;> nlinarith
  · have locations := changed.location_sum_le_three_distance (Ne.symm same)
    have receiverPositive := changed.location_pos receiver
    have sourcePositive := changed.location_pos source
    have receiverLength : changed.length receiver ≤ changed.location receiver := by
      simpa using (lengths receiver).le
    have sourceLength : changed.length source ≤ changed.location source := by
      simpa using (lengths source).le
    have receiverBound := mul_le_mul_of_nonneg_left receiverLength (by positivity : 0 ≤ tolerance / 100)
    have sourceBound := mul_le_mul_of_nonneg_left sourceLength (by positivity : 0 ≤ tolerance / 100)
    have receiverLocation := mul_le_mul_of_nonneg_left
      (show changed.location receiver ≤ 3 * |changed.location receiver - changed.location source| by linarith)
      tolerancePositive.le
    have sourceLocation := mul_le_mul_of_nonneg_left
      (show changed.location source ≤ 3 * |changed.location receiver - changed.location source| by linarith)
      tolerancePositive.le
    simp only [Scales.individualInteractionDistance, if_neg same]
    constructor <;> nlinarith [abs_nonneg (changed.location receiver - changed.location source)]

theorem Scales.eventually_weighted_interaction_radius_small (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {weight factor parameterRadius : ℝ}
    (weightPositive : 0 < weight) (factorPositive : 0 < factor)
    (parameterPositive : 0 < parameterRadius) :
    ∀ᶠ frequency : ℝ in atTop, ∀ receiver source : ℕ,
      let changed : Scales := {scales with frequency := frequency}
      1536 * weight * changed.radius receiver ≤
        factor * changed.individualInteractionDistance receiver source ∧
      8 * changed.radius source ≤
        parameterRadius * factor * changed.individualInteractionDistance receiver source := by
  let tolerance := min (factor / (1536 * weight)) (parameterRadius * factor / 8)
  have tolerancePositive : 0 < tolerance := by dsimp [tolerance]; positivity
  filter_upwards [scales.eventually_radius_interaction_small amplitudePositive ratioBound
    alphaPositive tolerancePositive] with frequency small receiver source
  let changed : Scales := {scales with frequency := frequency}
  have distancePositive := changed.individualInteractionDistance_pos receiver source
  have first := (small receiver source).1.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) distancePositive.le)
  have second := (small receiver source).2.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) distancePositive.le)
  change changed.radius receiver ≤ factor / (1536 * weight) * _ at first
  change changed.radius source ≤ parameterRadius * factor / 8 * _ at second
  have scaled := mul_le_mul_of_nonneg_left first (show 0 ≤ 1536 * weight by positivity)
  constructor
  · calc
      _ ≤ (1536 * weight) * (factor / (1536 * weight) * changed.individualInteractionDistance receiver source) := scaled
      _ = _ := by dsimp only [changed]; field_simp [weightPositive.ne']
  · linarith

theorem weighted_interaction_ratios_le {weight factor interaction receiverRadius sourceRadius
    parameterRadius displacement : ℝ}
    (weightPositive : 0 < weight) (factorPositive : 0 < factor)
    (interactionPositive : 0 < interaction) (parameterPositive : 0 < parameterRadius)
    (receiverSmall : 1536 * weight * receiverRadius ≤ factor * interaction)
    (sourceSmall : 8 * sourceRadius ≤ parameterRadius * factor * interaction)
    (clearance : (factor / 4) * interaction ≤ displacement) :
    2 * weight * receiverRadius / ((factor / 8) * interaction) ≤ 1 / 2 ∧
    96 * weight * receiverRadius / displacement ≤ 1 / 2 ∧
    sourceRadius / displacement ≤ parameterRadius := by
  have positive : 0 < displacement := lt_of_lt_of_le (by positivity) clearance
  have weightedClearance := mul_le_mul_of_nonneg_left clearance weightPositive.le
  have parameterClearance := mul_le_mul_of_nonneg_left clearance parameterPositive.le
  refine ⟨(div_le_iff₀ (by positivity)).mpr ?_, (div_le_iff₀ positive).mpr ?_,
    (div_le_iff₀ positive).mpr ?_⟩ <;> nlinarith [mul_pos factorPositive interactionPositive]

theorem Scales.eventually_weighted_actual_center_ratios (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {weight factor parameterRadius : ℝ}
    (weightPositive : 0 < weight) (factorPositive : 0 < factor)
    (parameterPositive : 0 < parameterRadius) :
    ∀ᶠ frequency : ℝ in atTop, ∀ receiver source : ℕ, ∀ first second : ℂ,
      let changed : Scales := {scales with frequency := frequency}
      (factor / 4) * changed.individualInteractionDistance receiver source ≤ ‖first - second‖ →
      2 * weight * changed.radius receiver /
          ((factor / 8) * changed.individualInteractionDistance receiver source) ≤ 1 / 2 ∧
      96 * weight * changed.radius receiver / ‖first - second‖ ≤ 1 / 2 ∧
      changed.radius source / ‖first - second‖ ≤ parameterRadius := by
  filter_upwards [scales.eventually_weighted_interaction_radius_small amplitudePositive
    ratioBound alphaPositive weightPositive factorPositive parameterPositive]
    with frequency small
  intro receiver source first second
  dsimp only
  intro clearance
  exact weighted_interaction_ratios_le weightPositive factorPositive
    (({scales with frequency := frequency} : Scales).individualInteractionDistance_pos receiver source)
    parameterPositive (small receiver source).1 (small receiver source).2 clearance

end EulerNonuniqueness.Paper
