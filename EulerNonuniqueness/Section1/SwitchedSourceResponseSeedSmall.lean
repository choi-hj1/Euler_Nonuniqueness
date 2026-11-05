import EulerNonuniqueness.Section1.TimedReceiverSourceAmplitudeSeedBudget
import EulerNonuniqueness.Section1.SlowSeedProfileSmallness
import EulerNonuniqueness.Section1.AdjacentSharpSourcePrefixSeedBudget
import EulerNonuniqueness.General.TwoRateExponentialResponse

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

private theorem switched_scalar_source_integrable
    {amplitude slope offset rate entry finish : ℝ} :
    IntervalIntegrable (fun time : ℝ => if time ≤ entry then amplitude * Real.exp (rate * (time - entry))
      else slope * (time - entry) + offset) volume 0 finish := by
  have first : Continuous (fun time : ℝ => amplitude * Real.exp (rate * (time - entry))) := by fun_prop
  have second : Continuous (fun time : ℝ => slope * (time - entry) + offset) := by fun_prop
  have piecewise : Integrable ((Iic entry).piecewise
      (fun time : ℝ => amplitude * Real.exp (rate * (time - entry)))
      (fun time : ℝ => slope * (time - entry) + offset)) (volume.restrict (uIoc 0 finish)) :=
    Integrable.piecewise measurableSet_Iic
    (first.intervalIntegrable (μ := volume) 0 finish).def'.integrable.integrableOn
    (second.intervalIntegrable (μ := volume) 0 finish).def'.integrable.integrableOn
  apply intervalIntegrable_iff.mpr
  simpa only [Set.piecewise, mem_Iic] using piecewise

private theorem switched_scalar_source_majorant
    {amplitude slope offset rate comparison entry time : ℝ}
    (amplitudeNonnegative : 0 ≤ amplitude) (slopeNonnegative : 0 ≤ slope)
    (offsetNonnegative : 0 ≤ offset) (comparisonPositive : 0 < comparison)
    (rateBound : comparison ≤ rate) :
    (if time ≤ entry then amplitude * Real.exp (rate * (time - entry))
      else slope * (time - entry) + offset) ≤
        (amplitude + slope / comparison + offset) * Real.exp (comparison * (time - entry)) := by
  by_cases before : time ≤ entry
  · rw [if_pos before]
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_right rateBound (sub_nonpos.mpr before))) amplitudeNonnegative).trans
      (mul_le_mul_of_nonneg_right
        ((le_add_of_nonneg_right (div_nonneg slopeNonnegative comparisonPositive.le)).trans
          (le_add_of_nonneg_right offsetNonnegative)) (Real.exp_pos _).le)
  · rw [if_neg before]
    have age : 0 ≤ time - entry := (sub_pos.mpr (lt_of_not_ge before)).le
    have exponential : 1 ≤ Real.exp (comparison * (time - entry)) := Real.one_le_exp_iff.mpr (mul_nonneg comparisonPositive.le age)
    have linear := Real.add_one_le_exp (comparison * (time - entry))
    have ageBound : time - entry ≤ Real.exp (comparison * (time - entry)) / comparison := by
      apply (le_div_iff₀ comparisonPositive).mpr
      nlinarith only [linear]
    have slopeBound := mul_le_mul_of_nonneg_left ageBound slopeNonnegative
    have offsetBound := mul_le_mul_of_nonneg_left exponential offsetNonnegative
    have extra := mul_nonneg amplitudeNonnegative (Real.exp_pos (comparison * (time - entry))).le
    ring_nf at slopeBound offsetBound extra ⊢
    linarith only [slopeBound, offsetBound, extra]

private theorem nearest_full_source_amplitude_bound (scales : Scales) (index : ℕ)
    (frequencyOne : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    {incoming outgoing extent magnitude distance neutralFactor neutral : ℝ}
    (incomingNonnegative : 0 ≤ incoming) (outgoingNonnegative : 0 ≤ outgoing)
    (extentNonnegative : 0 ≤ extent) (magnitudeNonnegative : 0 ≤ magnitude)
    (distanceNonnegative : 0 ≤ distance) (neutralNonnegative : 0 ≤ neutral)
    (neutralFactorNonnegative : 0 ≤ neutralFactor)
    (neutralBound : neutral ≤ neutralFactor * scales.length (index + 1) ^ 2) :
    let nu := Real.sqrt 2 * scales.omega index
    let amplitude := incoming * extent ^ 2 * scales.circulation (index + 1) * scales.length (index + 1) ^ 2 *
      (1 + (scales.location (index + 1))⁻¹) * magnitude +
      outgoing * scales.circulation (index + 1) * (scales.circulation (index + 1) / nu +
        (1 + distance) * scales.length (index + 1) ^ 2 + neutral)
    2 * amplitude / (scales.location index ^ 4 * nu) ≤
      2 * (4 * outgoing + 100 * (incoming * extent ^ 2 * magnitude + outgoing * (1 + distance + neutralFactor))) *
        scales.omega index * scales.seed index := by
  dsimp only
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < scales.ratio := lt_of_lt_of_le (by norm_num) ratioBound
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive index
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index + 1)
  have omegaOne := frequencyOne.trans (scales.omega_ge_frequency frequencyPositive (by linarith only [ratioBound]) index)
  have locationPositive := scales.location_pos index
  have nextLocationPositive := scales.location_pos (index + 1)
  have sqrtOne : (1 : ℝ) ≤ Real.sqrt 2 := by norm_num
  have nuPositive : 0 < Real.sqrt 2 * scales.omega index := by positivity
  let auxiliary := Real.sqrt 2 / scales.ratio
  have auxiliaryPositive : 0 < auxiliary := by dsimp only [auxiliary]; positivity
  have omegaNext : scales.omega (index + 1) = scales.omega index * scales.ratio := by
    simp only [Scales.omega, pow_succ]; ring
  have nuIdentity : auxiliary * scales.omega (index + 1) = Real.sqrt 2 * scales.omega index := by
    rw [omegaNext]
    dsimp only [auxiliary]
    field_simp
    ring
  have public := scales.adjacent_sharp_source_prefix_seed_budget_le frequencyPositive ratioPositive
    incomingNonnegative outgoingNonnegative extentNonnegative magnitudeNonnegative distanceNonnegative neutralFactorNonnegative
    auxiliaryPositive index (show scales.omega index ≤ Real.sqrt 2 * scales.omega index by nlinarith only [sqrtOne, omegaPositive])
    neutralNonnegative neutralBound
  rw [nuIdentity] at public
  have auxiliaryDenominator : 1 ≤ auxiliary * scales.ratio ^ 2 := by
    have identity : auxiliary * scales.ratio ^ 2 = Real.sqrt 2 * scales.ratio := by dsimp only [auxiliary]; field_simp; ring
    rw [identity]
    nlinarith only [sqrtOne, ratioBound]
  have coefficient : 4 * outgoing + 100 *
      (incoming * extent ^ 2 * magnitude / (auxiliary * scales.ratio ^ 2) + outgoing * (1 + distance + neutralFactor) / scales.ratio) ≤
      4 * outgoing + 100 * (incoming * extent ^ 2 * magnitude + outgoing * (1 + distance + neutralFactor)) := by
    have first := div_le_self (by positivity : 0 ≤ incoming * extent ^ 2 * magnitude) auxiliaryDenominator
    have second := div_le_self (by positivity : 0 ≤ outgoing * (1 + distance + neutralFactor))
      (show 1 ≤ scales.ratio by linarith only [ratioBound])
    linarith only [first, second]
  have seedNonnegative : 0 ≤ scales.seed index := by dsimp only [Scales.seed]; positivity
  have publicBound := public.trans (mul_le_mul_of_nonneg_right coefficient seedNonnegative)
  have powerBound : (2 : ℝ) ^ index ≤ scales.omega index := by
    have powers := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) ratioBound index
    have multiplication := mul_le_mul_of_nonneg_right frequencyOne (pow_nonneg ratioPositive.le index)
    exact powers.trans (by simpa only [one_mul, Scales.omega] using multiplication)
  have inverseLocation : (scales.location (index + 1))⁻¹ ≤ 2 * scales.omega index := by
    rw [scales.location_eq_inv_pow, inv_inv, pow_succ]
    nlinarith only [powerBound]
  have incomingFactor : 1 + (scales.location (index + 1))⁻¹ ≤ 48 * scales.omega index := by
    linarith only [inverseLocation, omegaOne]
  let common := incoming * extent ^ 2 * scales.circulation (index + 1) * scales.length (index + 1) ^ 2 * magnitude /
    (scales.location index ^ 4 * (Real.sqrt 2 * scales.omega index))
  have commonNonnegative : 0 ≤ common := by dsimp only [common]; positivity
  have locationIdentity : scales.location index = 2 * scales.location (index + 1) := by
    rw [scales.location_eq_inv_pow, scales.location_eq_inv_pow, pow_succ]
    field_simp
  have physicalIdentity : incoming * extent ^ 2 *
      (scales.circulation (index + 1) * scales.length (index + 1) ^ 2 /
        |scales.location index - scales.location (index + 1)| ^ 4 *
        (1 + scales.location index / scales.location (index + 1))) * magnitude /
      (Real.sqrt 2 * scales.omega index) = 48 * common := by
    rw [locationIdentity, abs_of_pos (by linarith only [nextLocationPositive])]
    rw [show 2 * scales.location (index + 1) - scales.location (index + 1) = scales.location (index + 1) by ring]
    dsimp only [common]
    rw [locationIdentity]
    field_simp [nextLocationPositive.ne', omegaPositive.ne', (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
    ring
  rw [physicalIdentity] at publicBound
  let outgoingPart := outgoing / scales.location index ^ 4 * scales.circulation (index + 1) *
    (scales.circulation (index + 1) / (Real.sqrt 2 * scales.omega index) ^ 2 +
      ((1 + distance) * scales.length (index + 1) ^ 2 + neutral) / (Real.sqrt 2 * scales.omega index))
  have outgoingPartNonnegative : 0 ≤ outgoingPart := by dsimp only [outgoingPart]; positivity
  have scaledOutgoing := mul_le_mul_of_nonneg_right omegaOne outgoingPartNonnegative
  have scaledIncoming := mul_le_mul_of_nonneg_left incomingFactor commonNonnegative
  have identity : 2 * (incoming * extent ^ 2 * scales.circulation (index + 1) * scales.length (index + 1) ^ 2 *
      (1 + (scales.location (index + 1))⁻¹) * magnitude + outgoing * scales.circulation (index + 1) *
      (scales.circulation (index + 1) / (Real.sqrt 2 * scales.omega index) +
        (1 + distance) * scales.length (index + 1) ^ 2 + neutral)) /
      (scales.location index ^ 4 * (Real.sqrt 2 * scales.omega index)) =
      2 * (common * (1 + (scales.location (index + 1))⁻¹) + outgoingPart) := by
    dsimp only [common, outgoingPart]
    field_simp [locationPositive.ne', omegaPositive.ne', (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
    ring
  rw [identity]
  have scaledPublic := mul_le_mul_of_nonneg_left publicBound omegaPositive.le
  dsimp only [outgoingPart] at scaledOutgoing ⊢
  nlinarith only [scaledOutgoing, scaledIncoming, scaledPublic]

theorem Scales.eventually_switched_source_response_seed_small (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) (alphaSmall : scales.alpha < 1)
    (ratioPower : 4 < scales.ratio ^ scales.alpha)
    {coefficient timingError incoming outgoing extent magnitudeMax distanceMax neutralFactor precision : ℝ}
    (_coefficientPositive : 0 < coefficient) (_coefficientSmall : coefficient < 1 / 8)
    (timingNonnegative : 0 ≤ timingError)
    (ratioSeparation : (Real.sqrt 2 + 1) * 8 ≤
      scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1))
    (sectionTime : ℝ) (incomingNonnegative : 0 ≤ incoming) (outgoingNonnegative : 0 ≤ outgoing)
    (extentNonnegative : 0 ≤ extent) (magnitudeNonnegative : 0 ≤ magnitudeMax)
    (distanceNonnegative : 0 ≤ distanceMax) (neutralFactorNonnegative : 0 ≤ neutralFactor)
    (precisionPositive : 0 < precision) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count index : ℕ, ∀ selected : Finset ℕ,
    (∀ source ∈ selected, index + 1 ≤ source ∧ source ≤ count) → ∀ actualTime : ℕ → ℝ,
    let changed : Scales := {scales with frequency := frequency}
    let origin := actualTime (index + 1)
    let growth := 2 * Real.sqrt 2 * changed.omega index
    let comparison := Real.sqrt 2 * changed.omega index
    0 ≤ origin →
    |actualTime (index + 1) - changed.predictedTime sectionTime count (index + 1)| ≤ timingError / changed.omega (index + 1) →
    (∀ source ∈ selected, |actualTime source - changed.predictedTime sectionTime count source| ≤ timingError / changed.omega source) →
    (∀ source ∈ selected, 0 ≤ actualTime source ∧ actualTime source ≤ origin) →
    (∀ source ∈ selected, comparison ≤ coefficient * changed.omega source) →
    ∀ magnitude distance neutral : ℕ → ℝ,
    (∀ source ∈ selected, 0 ≤ magnitude source ∧ magnitude source ≤ magnitudeMax) →
    (∀ source ∈ selected, 0 ≤ distance source ∧ distance source ≤ distanceMax) →
    (∀ source ∈ selected, 0 ≤ neutral source ∧ neutral source ≤ neutralFactor * changed.length source ^ 2) →
    ∀ rate finish endpoint : ℝ, 0 ≤ rate → rate ≤ comparison / 2 → 0 ≤ finish → endpoint ≤ 1 →
    changed.seed index * Real.exp (growth * (finish - origin)) ≤ endpoint →
    let sourceEnvelope := fun time => ∑ source ∈ selected,
      if time ≤ actualTime source then incoming * extent ^ 2 * changed.circulation source * changed.length source ^ 2 *
        (1 + (changed.location source)⁻¹) * magnitude source *
          Real.exp (coefficient * changed.omega source * (time - actualTime source))
      else outgoing * changed.circulation source * (changed.circulation source * (time - actualTime source) +
        (1 + distance source) * changed.length source ^ 2 + neutral source)
    IntervalIntegrable sourceEnvelope volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (rate * (finish - time)) * sourceEnvelope time) volume 0 finish ∧
    (∫ time in (0 : ℝ)..finish, Real.exp (rate * (finish - time)) * sourceEnvelope time) /
      changed.location index ^ 4 ≤ precision := by
  let constant := 2 * (4 * outgoing + 100 * (incoming * extent ^ 2 * magnitudeMax + outgoing * (1 + distanceMax + neutralFactor))) + 2
  have constantNonnegative : 0 ≤ constant := by dsimp only [constant]; positivity
  let accuracy := precision / (constant + 1)
  have accuracyPositive : 0 < accuracy := by dsimp only [accuracy]; positivity
  let auxiliary := Real.sqrt 2 / scales.ratio
  have ratioPositive : 0 < scales.ratio := lt_of_lt_of_le (by norm_num) ratioBound
  have auxiliaryPositive : 0 < auxiliary := by dsimp only [auxiliary]; positivity
  have auxiliaryOne : auxiliary ≤ 1 := by
    apply (div_le_one ratioPositive).mpr
    have upper : Real.sqrt 2 ≤ (2 : ℝ) := by
      nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
    exact upper.trans ratioBound
  have auxiliarySeparation : (auxiliary * scales.ratio + 1) * 8 ≤
      scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) := by
    simpa only [auxiliary, div_mul_cancel₀ _ ratioPositive.ne'] using ratioSeparation
  filter_upwards [scales.eventually_timed_receiver_source_amplitude_seed_budget ratioBound alphaPositive alphaSmall ratioPower
      auxiliaryPositive auxiliaryOne timingNonnegative auxiliarySeparation sectionTime incomingNonnegative outgoingNonnegative
      extentNonnegative magnitudeNonnegative distanceNonnegative neutralFactorNonnegative (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) < 1),
    scales.eventually_slow_seed_profile_small ratioBound alphaPositive (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) 1 accuracyPositive,
    scales.eventually_polynomial_seed_rpow_lt ratioBound alphaPositive 1 (by norm_num : (0 : ℝ) < 1) accuracyPositive,
    eventually_ge_atTop (1 : ℝ)] with frequency olderBudget slowSmall seedSmall frequencyOne
  intro count index selected selectedBounds actualTime
  dsimp only
  intro originNonnegative receiverTiming sourceTiming timeOrder sourceRates magnitude distance neutral magnitudeBounds distanceBounds neutralBounds
    rate finish endpoint rateNonnegative rateBound finishNonnegative endpointOne exposure
  let changed : Scales := {scales with frequency := frequency}
  let origin := actualTime (index + 1)
  let growth := 2 * Real.sqrt 2 * changed.omega index
  let comparison := Real.sqrt 2 * changed.omega index
  let term := fun source => incoming * extent ^ 2 * changed.circulation source * changed.length source ^ 2 *
      (1 + (changed.location source)⁻¹) * magnitude source +
    outgoing * changed.circulation source * (changed.circulation source / comparison +
      (1 + distance source) * changed.length source ^ 2 + neutral source)
  let amplitude := ∑ source ∈ selected, term source * Real.exp (comparison * (origin - actualTime source))
  let older := selected.filter (fun source => index + 2 ≤ source)
  let olderAmplitude := ∑ source ∈ older, term source * Real.exp (comparison * (origin - actualTime source))
  let nearestAmplitude := incoming * extent ^ 2 * changed.circulation (index + 1) * changed.length (index + 1) ^ 2 *
      (1 + (changed.location (index + 1))⁻¹) * magnitudeMax +
    outgoing * changed.circulation (index + 1) * (changed.circulation (index + 1) / comparison +
      (1 + distanceMax) * changed.length (index + 1) ^ 2 + neutralFactor * changed.length (index + 1) ^ 2)
  let sourceEnvelope := fun time => ∑ source ∈ selected,
    if time ≤ actualTime source then incoming * extent ^ 2 * changed.circulation source * changed.length source ^ 2 *
      (1 + (changed.location source)⁻¹) * magnitude source *
        Real.exp (coefficient * changed.omega source * (time - actualTime source))
    else outgoing * changed.circulation source * (changed.circulation source * (time - actualTime source) +
      (1 + distance source) * changed.length source ^ 2 + neutral source)
  change rate ≤ comparison / 2 at rateBound
  have frequencyPositive : 0 < frequency := zero_lt_one.trans_le frequencyOne
  have actualRatioPositive : 0 < changed.ratio := ratioPositive
  have omegaPositive := changed.omega_pos frequencyPositive actualRatioPositive index
  have omegaOne := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive (by linarith only [ratioBound]) index)
  have comparisonPositive : 0 < comparison := by dsimp only [comparison]; positivity
  have locationPositive := changed.location_pos index
  have seedNonnegative : 0 ≤ changed.seed index := by dsimp only [Scales.seed]; positivity
  have termNonnegative (source : ℕ) (member : source ∈ selected) : 0 ≤ term source := by
    have gamma := changed.circulation_pos frequencyPositive actualRatioPositive source
    have mag := (magnitudeBounds source member).1
    have dist := (distanceBounds source member).1
    have neu := (neutralBounds source member).1
    have loc := changed.location_pos source
    dsimp only [term]
    positivity
  have amplitudeNonnegative : 0 ≤ amplitude := Finset.sum_nonneg (fun source member =>
    mul_nonneg (termNonnegative source member) (Real.exp_pos _).le)
  have nearestNonnegative : 0 ≤ nearestAmplitude := by
    have gamma := changed.circulation_pos frequencyPositive actualRatioPositive (index + 1)
    have loc := changed.location_pos (index + 1)
    dsimp only [nearestAmplitude]
    positivity
  have amplitudeBound : amplitude ≤ nearestAmplitude + olderAmplitude := by
    have filters : selected.filter (fun source => ¬source = index + 1) = older := by
      ext source
      simp only [Finset.mem_filter, older]
      constructor
      · rintro ⟨member, different⟩
        exact ⟨member, by have := (selectedBounds source member).1; omega⟩
      · rintro ⟨member, above⟩
        exact ⟨member, by omega⟩
    have nearestFilter : selected.filter (fun source => source = index + 1) =
        if index + 1 ∈ selected then {index + 1} else ∅ := by ext source; simp; aesop
    have partition := Finset.sum_filter_add_sum_filter_not selected (fun source => source = index + 1)
      (fun source => term source * Real.exp (comparison * (origin - actualTime source)))
    rw [filters, nearestFilter] at partition
    dsimp only [amplitude, olderAmplitude]
    rw [← partition]
    apply add_le_add_right
    by_cases member : index + 1 ∈ selected
    · simp only [member, if_true, Finset.sum_singleton, origin, sub_self, mul_zero, Real.exp_zero, mul_one]
      dsimp only [term, nearestAmplitude]
      have gamma := changed.circulation_pos frequencyPositive actualRatioPositive (index + 1)
      have loc := changed.location_pos (index + 1)
      gcongr
      · exact (magnitudeBounds _ member).2
      · exact (distanceBounds _ member).2
      · exact (neutralBounds _ member).2
    · simpa only [member, if_false, Finset.sum_empty] using nearestNonnegative
  have olderBound := olderBudget count index older
    (fun source member => ⟨(Finset.mem_filter.mp member).2, (selectedBounds source (Finset.mem_filter.mp member).1).2⟩)
    actualTime receiverTiming
    (fun source member => sourceTiming source (Finset.mem_filter.mp member).1)
    (fun source member => (timeOrder source (Finset.mem_filter.mp member).1).2)
    magnitude distance neutral
    (fun source member => magnitudeBounds source (Finset.mem_filter.mp member).1)
    (fun source member => distanceBounds source (Finset.mem_filter.mp member).1)
    (fun source member => neutralBounds source (Finset.mem_filter.mp member).1)
  dsimp only at olderBound
  have comparisonAuxiliary : auxiliary * changed.omega (index + 1) = comparison := by
    have next : changed.omega (index + 1) = changed.omega index * changed.ratio := by simp only [Scales.omega, pow_succ]; ring
    rw [next]
    dsimp only [auxiliary, comparison, changed]
    field_simp
    ring
  have literalAuxiliary : auxiliary * ({scales with frequency := frequency} : Scales).omega (index + 1) = comparison := comparisonAuxiliary
  rw [literalAuxiliary] at olderBound
  simp only [one_mul, mul_one] at olderBound
  change (changed.omega index / changed.ratio) * olderAmplitude /
    (changed.location index ^ 4 * comparison ^ 2) ≤ changed.seed index / changed.ratio ^ 2 at olderBound
  have olderNormalized : 2 * olderAmplitude / (changed.location index ^ 4 * comparison) ≤
      2 * changed.omega index * changed.seed index := by
    have identity : 2 * olderAmplitude / (changed.location index ^ 4 * comparison) =
        ((changed.omega index / changed.ratio) * olderAmplitude /
          (changed.location index ^ 4 * comparison ^ 2)) * (2 * comparison * changed.ratio / changed.omega index) := by
      field_simp [omegaPositive.ne', actualRatioPositive.ne', locationPositive.ne', comparisonPositive.ne']
      ring
    rw [identity]
    have multiplied := mul_le_mul_of_nonneg_right olderBound
      (show 0 ≤ 2 * comparison * changed.ratio / changed.omega index by positivity)
    apply multiplied.trans
    have sqrtUpper : Real.sqrt 2 ≤ changed.ratio := by
      have upper : Real.sqrt 2 ≤ (2 : ℝ) := by
        nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
      exact upper.trans ratioBound
    have coefficientBound : 2 * comparison / (changed.ratio * changed.omega index) ≤ 2 := by
      dsimp only [comparison]
      apply (div_le_iff₀ (mul_pos actualRatioPositive omegaPositive)).mpr
      nlinarith only [mul_le_mul_of_nonneg_right sqrtUpper omegaPositive.le]
    have final := mul_le_mul_of_nonneg_right coefficientBound seedNonnegative
    have strengthened := mul_le_mul_of_nonneg_left omegaOne (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) seedNonnegative)
    apply (show _ ≤ 2 * changed.seed index from ?_).trans (by nlinarith only [strengthened])
    convert final using 1
    all_goals
      field_simp
      ring
  have nearestBound := nearest_full_source_amplitude_bound changed index frequencyOne ratioBound incomingNonnegative
    outgoingNonnegative extentNonnegative magnitudeNonnegative distanceNonnegative
    (show 0 ≤ neutralFactor * changed.length (index + 1) ^ 2 by positivity) neutralFactorNonnegative le_rfl
  change 2 * nearestAmplitude / (changed.location index ^ 4 * comparison) ≤ _ at nearestBound
  have normalizedAmplitude : 2 * amplitude / (changed.location index ^ 4 * comparison) ≤
      constant * changed.omega index * changed.seed index := by
    have scaled := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left amplitudeBound (by norm_num : (0 : ℝ) ≤ 2))
      (show 0 ≤ changed.location index ^ 4 * comparison by positivity)
    have split : 2 * (nearestAmplitude + olderAmplitude) / (changed.location index ^ 4 * comparison) =
        2 * nearestAmplitude / (changed.location index ^ 4 * comparison) +
          2 * olderAmplitude / (changed.location index ^ 4 * comparison) := by ring
    rw [split] at scaled
    apply scaled.trans
    dsimp only [constant]
    nlinarith only [nearestBound, olderNormalized]
  have sourceI : IntervalIntegrable sourceEnvelope volume 0 finish := by
    have each (source : ℕ) (_member : source ∈ selected) : IntervalIntegrable
        (fun time : ℝ => if time ≤ actualTime source then
          incoming * extent ^ 2 * changed.circulation source * changed.length source ^ 2 *
            (1 + (changed.location source)⁻¹) * magnitude source * Real.exp (coefficient * changed.omega source * (time - actualTime source))
          else outgoing * changed.circulation source * (changed.circulation source * (time - actualTime source) +
            (1 + distance source) * changed.length source ^ 2 + neutral source)) volume 0 finish := by
      have scalar := switched_scalar_source_integrable
        (amplitude := incoming * extent ^ 2 * changed.circulation source * changed.length source ^ 2 *
          (1 + (changed.location source)⁻¹) * magnitude source)
        (slope := outgoing * changed.circulation source ^ 2)
        (offset := outgoing * changed.circulation source * ((1 + distance source) * changed.length source ^ 2 + neutral source))
        (rate := coefficient * changed.omega source) (entry := actualTime source) (finish := finish)
      convert scalar using 1
      funext time
      split_ifs <;> ring
    convert IntervalIntegrable.sum selected each using 1
    funext time
    simp only [sourceEnvelope, Finset.sum_apply]
  have majorant (time : ℝ) : sourceEnvelope time ≤ amplitude * Real.exp (comparison * (time - origin)) := by
    dsimp only [sourceEnvelope, amplitude]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro source member
    have gamma := changed.circulation_pos frequencyPositive actualRatioPositive source
    have loc := changed.location_pos source
    have mag := (magnitudeBounds source member).1
    have dist := (distanceBounds source member).1
    have neu := (neutralBounds source member).1
    have scalar := switched_scalar_source_majorant
      (amplitude := incoming * extent ^ 2 * changed.circulation source * changed.length source ^ 2 *
        (1 + (changed.location source)⁻¹) * magnitude source)
      (slope := outgoing * changed.circulation source ^ 2)
      (offset := outgoing * changed.circulation source * ((1 + distance source) * changed.length source ^ 2 + neutral source))
      (entry := actualTime source) (time := time)
      (by positivity) (by positivity) (by positivity) comparisonPositive (sourceRates source member)
    have factor : Real.exp (comparison * (time - actualTime source)) =
        Real.exp (comparison * (origin - actualTime source)) * Real.exp (comparison * (time - origin)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [factor] at scalar
    convert scalar using 1
    · split_ifs <;> ring
    · dsimp only [term]
      ring
  have weightedI : IntervalIntegrable (fun time => Real.exp (-rate * time) * sourceEnvelope time) volume 0 finish := by
    simpa only [mul_comm] using sourceI.mul_continuousOn
      (show ContinuousOn (fun time : ℝ => Real.exp (-rate * time)) (uIcc 0 finish) by fun_prop)
  have kernelI : IntervalIntegrable (fun time => Real.exp (rate * (finish - time)) * sourceEnvelope time) volume 0 finish := by
    simpa only [mul_comm] using sourceI.mul_continuousOn
      (show ContinuousOn (fun time : ℝ => Real.exp (rate * (finish - time))) (uIcc 0 finish) by fun_prop)
  have response := intervalIntegral.exp_mul_integral_le_of_faster_exponential_majorant finishNonnegative
    (show rate < comparison by linarith only [rateBound, comparisonPositive]) amplitudeNonnegative weightedI (fun time _ => majorant time)
  have gap : comparison / 2 ≤ comparison - rate := by linarith only [rateBound]
  have denominator := div_le_div_of_nonneg_left amplitudeNonnegative (half_pos comparisonPositive) gap
  have responseBound := response.trans (mul_le_mul_of_nonneg_right denominator (Real.exp_pos _).le)
  have kernelIdentity : (∫ time in (0 : ℝ)..finish, Real.exp (rate * (finish - time)) * sourceEnvelope time) =
      Real.exp (rate * finish) * ∫ time in (0 : ℝ)..finish, Real.exp (-rate * time) * sourceEnvelope time := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro time _
    dsimp only
    have identity : Real.exp (rate * (finish - time)) = Real.exp (rate * finish) * Real.exp (-rate * time) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [identity]
    ring
  have absolute : (∫ time in (0 : ℝ)..finish, Real.exp (rate * (finish - time)) * sourceEnvelope time) /
      changed.location index ^ 4 ≤ constant * (changed.omega index * changed.seed index * Real.exp (comparison * (finish - origin))) := by
    rw [kernelIdentity]
    have normalized := div_le_div_of_nonneg_right responseBound (pow_nonneg locationPositive.le 4)
    have scaled := mul_le_mul_of_nonneg_right normalizedAmplitude (Real.exp_pos (comparison * (finish - origin))).le
    apply normalized.trans
    convert scaled using 1 <;> ring
  have small : changed.omega index * changed.seed index * Real.exp (comparison * (finish - origin)) < accuracy := by
    by_cases after : origin ≤ finish
    · have growthIdentity : comparison ≤ (1 / 2 : ℝ) * growth := by
        dsimp only [comparison, growth]
        ring_nf
        exact le_rfl
      have exposureOne := exposure.trans endpointOne
      have bound := slowSmall index growth comparison origin finish comparisonPositive.le growthIdentity after exposureOne
      simpa only [pow_one] using bound
    · have age : finish - origin ≤ 0 := sub_nonpos.mpr (le_of_not_ge after)
      have exponential : Real.exp (comparison * (finish - origin)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos comparisonPositive.le age)
      have bound := mul_le_mul_of_nonneg_left exponential (mul_nonneg omegaPositive.le seedNonnegative)
      have seedBound := seedSmall index
      simp only [pow_one, Real.rpow_one] at seedBound
      have bounded : changed.omega index * changed.seed index * Real.exp (comparison * (finish - origin)) ≤
          changed.omega index * changed.seed index := by simpa only [mul_one] using bound
      exact bounded.trans_lt seedBound
  refine ⟨sourceI, kernelI, absolute.trans ?_⟩
  have nonnegative : 0 ≤ changed.omega index * changed.seed index * Real.exp (comparison * (finish - origin)) := by positivity
  have enlarged : constant * (changed.omega index * changed.seed index * Real.exp (comparison * (finish - origin))) ≤
      (constant + 1) * (changed.omega index * changed.seed index * Real.exp (comparison * (finish - origin))) :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)) nonnegative
  have scaled := mul_lt_mul_of_pos_left small (by positivity : 0 < constant + 1)
  have cancel : (constant + 1) * accuracy = precision := by dsimp only [accuracy]; field_simp
  rw [cancel] at scaled
  exact (enlarged.trans_lt scaled).le

end EulerNonuniqueness.Paper
