import EulerNonuniqueness.Section1.TimedQuadraticCirculationSeedTail

noncomputable section

open Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

private theorem receiver_source_amplitude_term_le
    {circulation length location rate incoming outgoing extent magnitudeMax distanceMax neutralFactor magnitude distance neutral : ℝ}
    (circulationNonnegative : 0 ≤ circulation) (locationPositive : 0 < location) (ratePositive : 0 < rate)
    (lengthBound : length ^ 2 ≤ circulation / rate)
    (incomingNonnegative : 0 ≤ incoming) (outgoingNonnegative : 0 ≤ outgoing)
    (distanceNonnegative : 0 ≤ distanceMax)
    (neutralFactorNonnegative : 0 ≤ neutralFactor)
    (magnitudeBounds : 0 ≤ magnitude ∧ magnitude ≤ magnitudeMax)
    (distanceBound : distance ≤ distanceMax) (neutralBound : neutral ≤ neutralFactor * length ^ 2) :
    incoming * extent ^ 2 * circulation * length ^ 2 * (1 + location⁻¹) * magnitude +
      outgoing * circulation * (circulation / rate + (1 + distance) * length ^ 2 + neutral) ≤
      (incoming * extent ^ 2 * magnitudeMax + outgoing * (2 + distanceMax + neutralFactor)) / rate *
        ((1 + location⁻¹) * circulation ^ 2) := by
  have incomingBound : incoming * extent ^ 2 * circulation * length ^ 2 * (1 + location⁻¹) * magnitude ≤
      incoming * extent ^ 2 * circulation * (circulation / rate) * (1 + location⁻¹) * magnitudeMax := by
    gcongr
    · exact magnitudeBounds.1
    · exact magnitudeBounds.2
  have numeratorBound : circulation / rate + (1 + distance) * length ^ 2 + neutral ≤
      (2 + distanceMax + neutralFactor) * (circulation / rate) := by
    have first : circulation / rate + (1 + distance) * length ^ 2 + neutral ≤
        circulation / rate + (1 + distanceMax + neutralFactor) * length ^ 2 := by
      nlinarith only [neutralBound, mul_le_mul_of_nonneg_right distanceBound (sq_nonneg length)]
    have second := mul_le_mul_of_nonneg_left lengthBound
      (show 0 ≤ 1 + distanceMax + neutralFactor by positivity)
    nlinarith only [first, second]
  have outgoingBound := mul_le_mul_of_nonneg_left numeratorBound (mul_nonneg outgoingNonnegative circulationNonnegative)
  have extra := le_mul_of_one_le_left
    (show 0 ≤ outgoing * (2 + distanceMax + neutralFactor) * circulation ^ 2 / rate by positivity)
    (le_add_of_nonneg_right (inv_nonneg.mpr locationPositive.le))
  ring_nf at incomingBound outgoingBound extra ⊢
  linarith only [incomingBound, outgoingBound, extra]

theorem Scales.eventually_timed_receiver_source_amplitude_seed_budget (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) (alphaSmall : scales.alpha < 1)
    (ratioPower : 4 < scales.ratio ^ scales.alpha) {coefficient timingError : ℝ}
    (coefficientPositive : 0 < coefficient) (coefficientOne : coefficient ≤ 1)
    (timingErrorNonnegative : 0 ≤ timingError)
    (ratioSeparation : (coefficient * scales.ratio + 1) * 8 ≤
      scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1))
    (sectionTime : ℝ) {incoming outgoing extent magnitudeMax distanceMax neutralFactor receiverConstant tolerance : ℝ}
    (incomingNonnegative : 0 ≤ incoming) (outgoingNonnegative : 0 ≤ outgoing) (extentNonnegative : 0 ≤ extent)
    (magnitudeNonnegative : 0 ≤ magnitudeMax) (distanceNonnegative : 0 ≤ distanceMax)
    (neutralFactorNonnegative : 0 ≤ neutralFactor) (receiverNonnegative : 0 ≤ receiverConstant)
    (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count receiver : ℕ, ∀ selected : Finset ℕ,
      (∀ source ∈ selected, receiver + 2 ≤ source ∧ source ≤ count) → ∀ actualTime : ℕ → ℝ,
      let changed : Scales := {scales with frequency := frequency}
      |actualTime (receiver + 1) - changed.predictedTime sectionTime count (receiver + 1)| ≤
        timingError / changed.omega (receiver + 1) →
      (∀ source ∈ selected, |actualTime source - changed.predictedTime sectionTime count source| ≤ timingError / changed.omega source) →
      (∀ source ∈ selected, actualTime source ≤ actualTime (receiver + 1)) →
      ∀ magnitude distance neutral : ℕ → ℝ,
      (∀ source ∈ selected, 0 ≤ magnitude source ∧ magnitude source ≤ magnitudeMax) →
      (∀ source ∈ selected, 0 ≤ distance source ∧ distance source ≤ distanceMax) →
      (∀ source ∈ selected, 0 ≤ neutral source ∧ neutral source ≤ neutralFactor * changed.length source ^ 2) →
      let rate := coefficient * changed.omega (receiver + 1)
      let amplitude := ∑ source ∈ selected,
        (incoming * extent ^ 2 * changed.circulation source * changed.length source ^ 2 *
            (1 + (changed.location source)⁻¹) * magnitude source +
          outgoing * changed.circulation source * (changed.circulation source / rate +
            (1 + distance source) * changed.length source ^ 2 + neutral source)) *
          Real.exp (rate * (actualTime (receiver + 1) - actualTime source))
      (changed.omega receiver / changed.ratio) * receiverConstant * amplitude /
          (changed.location receiver ^ 4 * rate ^ 2) ≤
        tolerance * changed.seed receiver / changed.ratio ^ 2 := by
  let sourceConstant := incoming * extent ^ 2 * magnitudeMax + outgoing * (2 + distanceMax + neutralFactor)
  have sourceNonnegative : 0 ≤ sourceConstant := by
    dsimp only [sourceConstant]
    exact add_nonneg (mul_nonneg (mul_nonneg incomingNonnegative (pow_nonneg extentNonnegative 2)) magnitudeNonnegative) (by positivity)
  have ratioPositive : 0 < scales.ratio := by linarith only [ratioBound]
  let tailTolerance := tolerance * coefficient ^ 3 * scales.ratio ^ 4 / (receiverConstant * sourceConstant + 1)
  have tailPositive : 0 < tailTolerance := by dsimp only [tailTolerance]; positivity
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    scales.eventually_timed_quadratic_circulation_seed_tail ratioBound alphaPositive alphaSmall ratioPower
      (mul_nonneg coefficientPositive.le ratioPositive.le) timingErrorNonnegative ratioSeparation sectionTime 0 tailPositive]
    with frequency frequencyPositive tails
  intro count receiver selected selectedBounds actualTime
  dsimp only
  intro receiverTiming sourceTiming timeOrder magnitude distance neutral magnitudeBounds distanceBounds neutralBounds
  let changed : Scales := {scales with frequency := frequency}
  let rate := coefficient * changed.omega (receiver + 1)
  let quadraticSum := ∑ source ∈ selected, (1 + (changed.location source)⁻¹) * changed.circulation source ^ 2 *
    Real.exp (rate * (actualTime (receiver + 1) - actualTime source))
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive receiver
  have nextPositive := changed.omega_pos frequencyPositive ratioPositive (receiver + 1)
  have ratePositive : 0 < rate := mul_pos coefficientPositive nextPositive
  have omegaNext : changed.omega (receiver + 1) = changed.omega receiver * changed.ratio := by
    simp only [Scales.omega, pow_succ]; ring
  have rateIdentity : rate = coefficient * changed.ratio * changed.omega receiver := by dsimp only [rate]; rw [omegaNext]; ring
  have tail := tails count receiver selected selectedBounds actualTime receiverTiming sourceTiming timeOrder
  simp only [pow_zero, one_div] at tail
  have sourceLength (source : ℕ) (member : source ∈ selected) : changed.length source ^ 2 ≤ changed.circulation source / rate := by
    have sourcePositive := changed.omega_pos frequencyPositive ratioPositive source
    have omegaBound : changed.omega (receiver + 1) ≤ changed.omega source :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (show 1 ≤ changed.ratio by change 1 ≤ scales.ratio; linarith only [ratioBound])
        (by have := (selectedBounds source member).1; omega)) frequencyPositive.le
    have rateBound : rate ≤ changed.omega source :=
      (mul_le_of_le_one_left nextPositive.le coefficientOne).trans omegaBound
    have identity : changed.circulation source / changed.omega source = 2 * Real.pi * changed.length source ^ 2 := by
      rw [Scales.circulation]; field_simp; ring
    have base : changed.length source ^ 2 ≤ changed.circulation source / changed.omega source := by
      rw [identity]
      nlinarith [mul_nonneg (show 0 ≤ 2 * Real.pi - 1 by linarith [Real.pi_gt_three]) (sq_nonneg (changed.length source))]
    exact base.trans (div_le_div_of_nonneg_left (changed.circulation_pos frequencyPositive ratioPositive source).le ratePositive rateBound)
  have amplitudeBound := Finset.sum_le_sum (fun source member => mul_le_mul_of_nonneg_right
    (receiver_source_amplitude_term_le (extent := extent) (changed.circulation_pos frequencyPositive ratioPositive source).le
      (changed.location_pos source) ratePositive (sourceLength source member) incomingNonnegative outgoingNonnegative
      distanceNonnegative neutralFactorNonnegative (magnitudeBounds source member)
      (distanceBounds source member).2 (neutralBounds source member).2)
    (Real.exp_pos (rate * (actualTime (receiver + 1) - actualTime source))).le)
  have quadraticBound : quadraticSum / (changed.omega receiver ^ 2 * changed.location receiver ^ 4) ≤
      tailTolerance * changed.seed receiver / changed.ratio ^ 2 := by
    apply le_trans _ tail
    rw [Finset.mul_sum]
    dsimp only [quadraticSum]
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro source member
    have locationPositive := changed.location_pos source
    have one : 1 ≤ 1 + changed.omega receiver * (actualTime (receiver + 1) - actualTime source) :=
      le_add_of_nonneg_right (mul_nonneg omegaPositive.le (sub_nonneg.mpr (timeOrder source member)))
    have actual := le_mul_of_one_le_right
      (show 0 ≤ (1 + (changed.location source)⁻¹) * changed.circulation source ^ 2 *
        Real.exp (rate * (actualTime (receiver + 1) - actualTime source)) /
        (changed.omega receiver ^ 2 * changed.location receiver ^ 4) by positivity) one
    convert actual using 1
    rw [rateIdentity]
    ring
  have amplitudeNormalized : (∑ source ∈ selected,
      (incoming * extent ^ 2 * changed.circulation source * changed.length source ^ 2 * (1 + (changed.location source)⁻¹) * magnitude source +
        outgoing * changed.circulation source * (changed.circulation source / rate + (1 + distance source) * changed.length source ^ 2 + neutral source)) *
        Real.exp (rate * (actualTime (receiver + 1) - actualTime source))) ≤ sourceConstant / rate * quadraticSum := by
    apply amplitudeBound.trans_eq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro source _
    dsimp only [sourceConstant]
    ring
  have scaled := mul_le_mul_of_nonneg_left amplitudeNormalized
    (show 0 ≤ (changed.omega receiver / changed.ratio) * receiverConstant / (changed.location receiver ^ 4 * rate ^ 2) by positivity)
  have normalization : (changed.omega receiver / changed.ratio) * receiverConstant /
      (changed.location receiver ^ 4 * rate ^ 2) * (sourceConstant / rate * quadraticSum) =
      (receiverConstant * sourceConstant / (coefficient ^ 3 * changed.ratio ^ 4)) *
        (quadraticSum / (changed.omega receiver ^ 2 * changed.location receiver ^ 4)) := by
    rw [rateIdentity]
    field_simp [omegaPositive.ne', coefficientPositive.ne', ratioPositive.ne', (changed.location_pos receiver).ne']
    ring
  rw [normalization] at scaled
  have final := scaled.trans (mul_le_mul_of_nonneg_left quadraticBound
    (show 0 ≤ receiverConstant * sourceConstant / (coefficient ^ 3 * changed.ratio ^ 4) by positivity))
  have coefficientBound : (receiverConstant * sourceConstant / (coefficient ^ 3 * changed.ratio ^ 4)) * tailTolerance ≤ tolerance := by
    have actual := (div_le_one (show 0 < receiverConstant * sourceConstant + 1 by positivity)).mpr
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
    have multiplied := mul_le_mul_of_nonneg_right actual tolerancePositive.le
    dsimp only [tailTolerance]
    convert multiplied using 1 <;> (field_simp; all_goals ring)
  have seedNonnegative : 0 ≤ changed.seed receiver / changed.ratio ^ 2 := by dsimp only [Scales.seed]; positivity
  have result := final.trans (by
    convert mul_le_mul_of_nonneg_right coefficientBound seedNonnegative using 1
    ring)
  convert result using 1 <;> (dsimp only [changed]; ring)

end EulerNonuniqueness.Paper
