import EulerNonuniqueness.Section1.TimedQuadraticCirculationSeedTail
import EulerNonuniqueness.Section1.DyadicSeparation

noncomputable section

open Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

private theorem older_sharp_source_bound (scales : Scales)
    (frequencyPositive : 0 < scales.frequency) (ratioOne : 1 ≤ scales.ratio)
    {incoming outgoing extent magnitudeMax distanceMax neutralFactor coefficient weight : ℝ}
    (incomingNonnegative : 0 ≤ incoming) (outgoingNonnegative : 0 ≤ outgoing)
    (magnitudeNonnegative : 0 ≤ magnitudeMax)
    (distanceNonnegative : 0 ≤ distanceMax) (neutralFactorNonnegative : 0 ≤ neutralFactor)
    (coefficientPositive : 0 < coefficient) {receiver source : ℕ} (below : receiver < source)
    (weightBound : scales.omega receiver ≤ weight) {magnitude distance neutral : ℝ}
    (magnitudeBounds : 0 ≤ magnitude ∧ magnitude ≤ magnitudeMax)
    (distanceBounds : 0 ≤ distance ∧ distance ≤ distanceMax)
    (neutralBounds : 0 ≤ neutral ∧ neutral ≤ neutralFactor * scales.length source ^ 2) :
    incoming * extent ^ 2 * (scales.circulation source * scales.length source ^ 2 /
        |scales.location receiver - scales.location source| ^ 4 *
        (1 + scales.location receiver / scales.location source)) * magnitude / (coefficient * scales.omega source) +
      outgoing / scales.location receiver ^ 4 * scales.circulation source *
        (scales.circulation source / weight ^ 2 + ((1 + distance) * scales.length source ^ 2 + neutral) / weight) ≤
      (16 * incoming * extent ^ 2 * magnitudeMax / coefficient + outgoing * (2 + distanceMax + neutralFactor)) *
        ((1 + (scales.location source)⁻¹) * scales.circulation source ^ 2 /
          (scales.omega receiver ^ 2 * scales.location receiver ^ 4)) := by
  have ratioPositive := zero_lt_one.trans_le ratioOne
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive receiver
  have sourcePositive := scales.omega_pos frequencyPositive ratioPositive source
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive source
  have receiverLocation := scales.location_pos receiver
  have sourceLocation := scales.location_pos source
  have gapPositive := scales.location_distance_pos (Nat.ne_of_lt below)
  have omegaBound : scales.omega receiver ≤ scales.omega source :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ratioOne below.le) frequencyPositive.le
  have weightPositive := omegaPositive.trans_le weightBound
  have gapBound : scales.location receiver / 2 ≤ |scales.location receiver - scales.location source| := by
    have separated := scales.location_le_half_of_lt below
    rw [abs_of_nonneg (by linarith : 0 ≤ scales.location receiver - scales.location source)]
    linarith
  have lengthCirculation : scales.length source ^ 2 ≤ scales.circulation source / scales.omega receiver := by
    have identity : scales.circulation source / scales.omega source = 2 * Real.pi * scales.length source ^ 2 := by
      rw [Scales.circulation]; field_simp; ring
    have first : scales.length source ^ 2 ≤ scales.circulation source / scales.omega source := by
      rw [identity]
      nlinarith [mul_nonneg (show 0 ≤ 2 * Real.pi - 1 by linarith [Real.pi_gt_three]) (sq_nonneg (scales.length source))]
    exact first.trans (div_le_div_of_nonneg_left circulationPositive.le omegaPositive omegaBound)
  have ratioBound : 1 + scales.location receiver / scales.location source ≤ 1 + (scales.location source)⁻¹ := by
    have actual := div_le_div_of_nonneg_right (scales.location_le_one receiver) sourceLocation.le
    simpa only [one_div] using add_le_add_left actual 1
  have incomingBound : incoming * extent ^ 2 * (scales.circulation source * scales.length source ^ 2 /
      |scales.location receiver - scales.location source| ^ 4 *
      (1 + scales.location receiver / scales.location source)) * magnitude / (coefficient * scales.omega source) ≤
      incoming * extent ^ 2 * (scales.circulation source * (scales.circulation source / scales.omega receiver) /
        (scales.location receiver / 2) ^ 4 * (1 + (scales.location source)⁻¹)) * magnitudeMax /
        (coefficient * scales.omega receiver) := by
    gcongr
    · exact magnitudeBounds.1
    · exact magnitudeBounds.2
  have numeratorBound : (1 + distance) * scales.length source ^ 2 + neutral ≤
      (1 + distanceMax + neutralFactor) * (scales.circulation source / scales.omega receiver) := by
    calc
      _ ≤ (1 + distanceMax + neutralFactor) * scales.length source ^ 2 := by
        nlinarith only [neutralBounds.2, mul_le_mul_of_nonneg_right distanceBounds.2 (sq_nonneg (scales.length source))]
      _ ≤ _ := mul_le_mul_of_nonneg_left lengthCirculation (by positivity)
  have bracketBound : scales.circulation source / weight ^ 2 +
      ((1 + distance) * scales.length source ^ 2 + neutral) / weight ≤
      (2 + distanceMax + neutralFactor) * scales.circulation source / scales.omega receiver ^ 2 := by
    have quadratic := div_le_div_of_nonneg_left circulationPositive.le (sq_pos_of_pos omegaPositive)
      (pow_le_pow_left₀ omegaPositive.le weightBound 2)
    have linear := (div_le_div_of_nonneg_right numeratorBound weightPositive.le).trans
      (div_le_div_of_nonneg_left (by positivity : 0 ≤ (1 + distanceMax + neutralFactor) *
        (scales.circulation source / scales.omega receiver)) omegaPositive weightBound)
    convert add_le_add quadratic linear using 1
    ring
  have outgoingBound := mul_le_mul_of_nonneg_left bracketBound
    (show 0 ≤ outgoing / scales.location receiver ^ 4 * scales.circulation source by positivity)
  have extra := le_mul_of_one_le_left
    (show 0 ≤ outgoing * (2 + distanceMax + neutralFactor) * scales.circulation source ^ 2 /
      (scales.omega receiver ^ 2 * scales.location receiver ^ 4) by positivity)
    (le_add_of_nonneg_right (inv_nonneg.mpr sourceLocation.le))
  have incomingNormalized : incoming * extent ^ 2 *
      (scales.circulation source * (scales.circulation source / scales.omega receiver) /
        (scales.location receiver / 2) ^ 4 * (1 + (scales.location source)⁻¹)) * magnitudeMax /
        (coefficient * scales.omega receiver) =
      (16 * incoming * extent ^ 2 * magnitudeMax / coefficient) *
        ((1 + (scales.location source)⁻¹) * scales.circulation source ^ 2 /
          (scales.omega receiver ^ 2 * scales.location receiver ^ 4)) := by ring
  rw [incomingNormalized] at incomingBound
  ring_nf at incomingBound outgoingBound extra ⊢
  linarith only [incomingBound, outgoingBound, extra]

theorem Scales.eventually_timed_older_sharp_source_prefix_seed_budget (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) (alphaSmall : scales.alpha < 1)
    (ratioPower : 4 < scales.ratio ^ scales.alpha) {growth timingError : ℝ} (growthOne : 1 ≤ growth)
    (timingErrorNonnegative : 0 ≤ timingError)
    (ratioSeparation : (growth + 1) * 8 ≤ scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1))
    (sectionTime : ℝ) {incoming outgoing extent magnitudeMax distanceMax neutralFactor coefficient tolerance : ℝ}
    (incomingNonnegative : 0 ≤ incoming) (outgoingNonnegative : 0 ≤ outgoing)
    (extentNonnegative : 0 ≤ extent) (magnitudeNonnegative : 0 ≤ magnitudeMax)
    (distanceNonnegative : 0 ≤ distanceMax) (neutralFactorNonnegative : 0 ≤ neutralFactor)
    (coefficientPositive : 0 < coefficient) (tolerancePositive : 0 < tolerance) :
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
      let weight := growth * changed.omega receiver
      (∑ source ∈ selected,
        (incoming * extent ^ 2 * (changed.circulation source * changed.length source ^ 2 /
            |changed.location receiver - changed.location source| ^ 4 *
            (1 + changed.location receiver / changed.location source)) * magnitude source / (coefficient * changed.omega source) +
          outgoing / changed.location receiver ^ 4 * changed.circulation source *
            (changed.circulation source / weight ^ 2 + ((1 + distance source) * changed.length source ^ 2 + neutral source) / weight)) *
          Real.exp (weight * (actualTime (receiver + 1) - actualTime source))) ≤
        tolerance * changed.seed receiver / changed.ratio ^ 2 := by
  let constant := 16 * incoming * extent ^ 2 * magnitudeMax / coefficient + outgoing * (2 + distanceMax + neutralFactor)
  have constantNonnegative : 0 ≤ constant := by
    dsimp only [constant]
    exact add_nonneg (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) incomingNonnegative)
      (pow_nonneg extentNonnegative 2)) magnitudeNonnegative) coefficientPositive.le) (by positivity)
  have smallerPositive : 0 < tolerance / (constant + 1) := div_pos tolerancePositive (by positivity)
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    scales.eventually_timed_quadratic_circulation_seed_tail ratioBound alphaPositive alphaSmall ratioPower
      (zero_le_one.trans growthOne) timingErrorNonnegative ratioSeparation sectionTime 0 smallerPositive]
    with frequency frequencyPositive tails
  intro count receiver selected selectedBounds actualTime
  dsimp only
  intro receiverTiming sourceTiming timeOrder magnitude distance neutral magnitudeBounds distanceBounds neutralBounds
  let changed : Scales := {scales with frequency := frequency}
  have ratioOne : 1 ≤ changed.ratio := (by norm_num : (1 : ℝ) ≤ 2).trans ratioBound
  have omegaPositive := changed.omega_pos frequencyPositive (zero_lt_one.trans_le ratioOne) receiver
  have tail := tails count receiver selected selectedBounds actualTime receiverTiming sourceTiming timeOrder
  simp only [pow_zero, one_div] at tail
  have termBound (source : ℕ) (member : source ∈ selected) := older_sharp_source_bound changed frequencyPositive ratioOne (extent := extent)
    incomingNonnegative outgoingNonnegative magnitudeNonnegative distanceNonnegative neutralFactorNonnegative
    coefficientPositive (show receiver < source by have := (selectedBounds source member).1; omega)
    (show changed.omega receiver ≤ growth * changed.omega receiver by nlinarith only [growthOne, omegaPositive])
    (magnitudeBounds source member) (distanceBounds source member) (neutralBounds source member)
  have sumBound := Finset.sum_le_sum (fun source member =>
    mul_le_mul_of_nonneg_right (termBound source member)
      (Real.exp_pos (growth * changed.omega receiver * (actualTime (receiver + 1) - actualTime source))).le)
  have larger : (∑ source ∈ selected,
      ((1 + (changed.location source)⁻¹) * changed.circulation source ^ 2 /
        (changed.omega receiver ^ 2 * changed.location receiver ^ 4)) *
          Real.exp (growth * changed.omega receiver * (actualTime (receiver + 1) - actualTime source))) ≤
      (changed.omega receiver ^ 2 * changed.location receiver ^ 4)⁻¹ *
        (∑ source ∈ selected, (1 + (changed.location source)⁻¹) * changed.circulation source ^ 2 *
          (1 + changed.omega receiver * (actualTime (receiver + 1) - actualTime source)) *
          Real.exp (growth * changed.omega receiver * (actualTime (receiver + 1) - actualTime source))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro source member
    have locationPositive := changed.location_pos source
    have one : 1 ≤ 1 + changed.omega receiver * (actualTime (receiver + 1) - actualTime source) :=
      le_add_of_nonneg_right (mul_nonneg omegaPositive.le (sub_nonneg.mpr (timeOrder source member)))
    have actual := le_mul_of_one_le_right
      (show 0 ≤ (1 + (changed.location source)⁻¹) * changed.circulation source ^ 2 *
        Real.exp (growth * changed.omega receiver * (actualTime (receiver + 1) - actualTime source)) /
        (changed.omega receiver ^ 2 * changed.location receiver ^ 4) by positivity) one
    convert actual using 1 <;> ring
  have summed : (∑ source ∈ selected,
      (incoming * extent ^ 2 * (changed.circulation source * changed.length source ^ 2 /
          |changed.location receiver - changed.location source| ^ 4 * (1 + changed.location receiver / changed.location source)) *
          magnitude source / (coefficient * changed.omega source) + outgoing / changed.location receiver ^ 4 * changed.circulation source *
          (changed.circulation source / (growth * changed.omega receiver) ^ 2 +
            ((1 + distance source) * changed.length source ^ 2 + neutral source) / (growth * changed.omega receiver))) *
        Real.exp (growth * changed.omega receiver * (actualTime (receiver + 1) - actualTime source))) ≤
      constant * (tolerance / (constant + 1) * changed.seed receiver / changed.ratio ^ 2) := by
    apply sumBound.trans
    convert mul_le_mul_of_nonneg_left (larger.trans tail) constantNonnegative using 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro source member
    dsimp only [constant]
    ring
  apply summed.trans
  have seedNonnegative : 0 ≤ changed.seed receiver / changed.ratio ^ 2 := by dsimp only [Scales.seed]; positivity
  have coefficientBound : constant * (tolerance / (constant + 1)) ≤ tolerance := by
    have actual := (div_le_one (by positivity : 0 < constant + 1)).mpr (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
    convert mul_le_mul_of_nonneg_right actual tolerancePositive.le using 1 <;> ring
  convert mul_le_mul_of_nonneg_right coefficientBound seedNonnegative using 1 <;> ring

end EulerNonuniqueness.Paper
