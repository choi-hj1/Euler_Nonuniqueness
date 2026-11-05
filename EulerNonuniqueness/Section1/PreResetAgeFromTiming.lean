import EulerNonuniqueness.Section5.Delay
import EulerNonuniqueness.Section1.UniformScaleBounds

noncomputable section

open Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

private theorem scaled_delay_kernel_Ico_le (scales : Scales)
    (frequencyPositive : 0 < scales.frequency) (ratioGreaterOne : 1 < scales.ratio)
    (alphaSmall : scales.alpha < 1) (receiver source : ℕ) (ordered : receiver + 1 ≤ source) :
    scales.omega receiver *
        (∑ index ∈ Finset.Ico (receiver + 1) source,
          scales.omega (index + 1) ^ scales.alpha / scales.omega index) ≤
      scales.omega (receiver + 1) ^ scales.alpha / (scales.ratio ^ (1 - scales.alpha) - 1) := by
  have ratioPositive : 0 < scales.ratio := zero_lt_one.trans ratioGreaterOne
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive receiver
  let shifted : Scales := {scales with frequency := scales.omega receiver}
  have shiftedOmega (index : ℕ) : shifted.omega index = scales.omega (receiver + index) := by
    simp only [shifted, Scales.omega, pow_add]
    ring
  have summable := shifted.delay_summable omegaPositive ratioGreaterOne alphaSmall
  have finiteBound := summable.sum_le_tsum (Finset.range (source - (receiver + 1)))
    (fun index _ => div_nonneg (Real.rpow_nonneg
      (shifted.omega_pos omegaPositive ratioPositive _).le _) (shifted.omega_pos omegaPositive ratioPositive _).le)
  have reindex :
      (∑ index ∈ Finset.range (source - (receiver + 1)),
        shifted.omega (index + 2) ^ scales.alpha / shifted.omega (index + 1)) =
      ∑ index ∈ Finset.Ico (receiver + 1) source,
        scales.omega (index + 1) ^ scales.alpha / scales.omega index := by
    have shift := Finset.sum_Ico_add'
      (fun index => scales.omega (index + 1) ^ scales.alpha / scales.omega index)
      0 (source - (receiver + 1)) (receiver + 1)
    simpa only [shiftedOmega, ← Finset.range_eq_Ico, zero_add,
      Nat.sub_add_cancel ordered, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      show (1 + 1 : ℕ) = 2 by rfl] using shift
  rw [reindex] at finiteBound
  have scaled := mul_le_mul_of_nonneg_left finiteBound omegaPositive.le
  rw [shifted.delay_sum omegaPositive ratioGreaterOne alphaSmall] at scaled
  have normalization : scales.omega receiver *
      (shifted.frequency ^ (scales.alpha - 1) * scales.ratio ^ (2 * scales.alpha - 1) /
        (1 - scales.ratio ^ (scales.alpha - 1))) =
      scales.omega (receiver + 1) ^ scales.alpha / (scales.ratio ^ (1 - scales.alpha) - 1) := by
    have nextOmega : scales.omega (receiver + 1) = scales.omega receiver * scales.ratio := by
      simp only [Scales.omega, pow_succ]
      ring
    have ratioPowerPositive : 0 < scales.ratio ^ scales.alpha := Real.rpow_pos_of_pos ratioPositive _
    have ratioPowerSmall : scales.ratio ^ scales.alpha < scales.ratio := by
      simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt ratioGreaterOne alphaSmall
    have firstDenominator : 1 - scales.ratio ^ scales.alpha / scales.ratio ≠ 0 := by
      have := (div_lt_one ratioPositive).mpr ratioPowerSmall
      linarith
    have secondDenominator : scales.ratio / scales.ratio ^ scales.alpha - 1 ≠ 0 := by
      have := (one_lt_div ratioPowerPositive).mpr ratioPowerSmall
      linarith
    dsimp only [shifted]
    rw [nextOmega, Real.mul_rpow omegaPositive.le ratioPositive.le,
      Real.rpow_sub omegaPositive, Real.rpow_one,
      Real.rpow_sub ratioPositive, Real.rpow_one,
      Real.rpow_sub ratioPositive, Real.rpow_one,
      Real.rpow_sub ratioPositive, Real.rpow_one,
      show 2 * scales.alpha = scales.alpha + scales.alpha by ring,
      Real.rpow_add ratioPositive]
    have denominatorIdentity : 1 - scales.ratio ^ scales.alpha / scales.ratio =
        (scales.ratio ^ scales.alpha / scales.ratio) *
          (scales.ratio / scales.ratio ^ scales.alpha - 1) := by
      field_simp [ratioPositive.ne', ratioPowerPositive.ne']
      ring
    rw [denominatorIdentity]
    generalize denominatorSymbol : scales.ratio / scales.ratio ^ scales.alpha - 1 = denominator at *
    field_simp [omegaPositive.ne', ratioPositive.ne', ratioPowerPositive.ne',
      firstDenominator, secondDenominator]
    ring
  exact scaled.trans_eq normalization

theorem Scales.eventually_prereset_age_le_of_timing_close (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (alphaSmall : scales.alpha < 1) (sectionTime : ℝ)
    {timingError : ℝ} (timingErrorNonnegative : 0 ≤ timingError) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count receiver source : ℕ,
      receiver + 2 ≤ source → source ≤ count → ∀ actualTime : ℕ → ℝ,
      let changed : Scales := {scales with frequency := frequency}
      |actualTime (receiver + 1) - changed.predictedTime sectionTime count (receiver + 1)| ≤
        timingError / changed.omega (receiver + 1) →
      |actualTime source - changed.predictedTime sectionTime count source| ≤
        timingError / changed.omega source →
      actualTime source ≤ actualTime (receiver + 1) →
      0 ≤ actualTime (receiver + 1) - actualTime source ∧
      changed.omega receiver * (actualTime (receiver + 1) - actualTime source) ≤
        8 * changed.omega (receiver + 1) ^ changed.alpha /
          (changed.ratio ^ (1 - changed.alpha) - 1) := by
  have ratioGreaterOne : 1 < scales.ratio := by linarith only [ratioBound]
  have ratioPositive : 0 < scales.ratio := zero_lt_one.trans ratioGreaterOne
  have denominatorPositive : 0 < scales.ratio ^ (1 - scales.alpha) - 1 :=
    sub_pos.mpr (Real.one_lt_rpow ratioGreaterOne (sub_pos.mpr alphaSmall))
  let remainder := sectionTime + (-Real.log (Real.sqrt 3) - Real.log 2 +
    Real.log (Real.sqrt 2) - 2 * Real.log scales.ratio) / (2 * Real.sqrt 2)
  have powerGrowth : Tendsto (fun frequency : ℝ => frequency ^ scales.alpha) atTop atTop :=
    tendsto_rpow_atTop alphaPositive
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    powerGrowth.eventually (eventually_ge_atTop remainder),
    powerGrowth.eventually (eventually_ge_atTop
      (timingError * (scales.ratio ^ (1 - scales.alpha) - 1) / 2))]
    with frequency frequencyOne remainderSmall timingSmall
  intro count receiver source older sourceBound actualTime
  dsimp only
  intro receiverTiming sourceTiming timeOrder
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have omegaPositive (index : ℕ) : 0 < changed.omega index :=
    changed.omega_pos frequencyPositive ratioPositive index
  have omegaMonotone {first second : ℕ} (ordered : first ≤ second) :
      changed.omega first ≤ changed.omega second :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ratioGreaterOne.le ordered) frequencyPositive.le
  have powerLarge (index : ℕ) : frequency ^ scales.alpha ≤ changed.omega index ^ changed.alpha :=
    Real.rpow_le_rpow frequencyPositive.le
      (changed.omega_ge_frequency frequencyPositive ratioGreaterOne.le index) alphaPositive.le
  have sqrtOne : 1 ≤ Real.sqrt 2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have leadingBound : 4 / (2 * Real.sqrt 2) ≤ (2 : ℝ) :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith only [sqrtOne])
  have delayUpper (index : ℕ) : changed.delay sectionTime index ≤
      4 * (changed.omega (index + 1) ^ changed.alpha / changed.omega index) := by
    have kernelNonnegative : 0 ≤ changed.omega (index + 1) ^ changed.alpha / changed.omega index :=
      div_nonneg (Real.rpow_nonneg (omegaPositive _).le _) (omegaPositive _).le
    have leading := mul_le_mul_of_nonneg_right leadingBound kernelNonnegative
    have remainderBound : remainder ≤ changed.omega (index + 1) ^ changed.alpha :=
      remainderSmall.trans (powerLarge _)
    have remainderTerm := mul_le_mul_of_nonneg_right remainderBound (inv_nonneg.mpr (omegaPositive index).le)
    have remainderTerm' : remainder * (changed.omega index)⁻¹ ≤
        changed.omega (index + 1) ^ changed.alpha / changed.omega index := by
      simpa only [div_eq_mul_inv] using remainderTerm
    have subtractedNonnegative : 0 ≤ (4 * Real.log 2 / (2 * Real.sqrt 2)) *
        (((index : ℝ) + 1) / changed.omega index) := by
      have logNonnegative : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have currentPositive := omegaPositive index
      positivity
    rw [changed.actual_delay_expansion frequencyPositive ratioPositive]
    change (4 / (2 * Real.sqrt 2)) *
        (changed.omega (index + 1) ^ changed.alpha / changed.omega index) -
        (4 * Real.log 2 / (2 * Real.sqrt 2)) * (((index : ℝ) + 1) / changed.omega index) +
        remainder * (changed.omega index)⁻¹ ≤ _
    nlinarith only [leading, remainderTerm', subtractedNonnegative, kernelNonnegative]
  have predictedDifference : changed.predictedTime sectionTime count (receiver + 1) -
      changed.predictedTime sectionTime count source =
      ∑ index ∈ Finset.Ico (receiver + 1) source, changed.delay sectionTime index := by
    have split := Finset.sum_Ico_consecutive (changed.delay sectionTime)
      (show receiver + 1 ≤ source by omega) sourceBound
    change (∑ index ∈ Finset.Ico (receiver + 1) count, changed.delay sectionTime index) -
      (∑ index ∈ Finset.Ico source count, changed.delay sectionTime index) = _
    linarith only [split]
  have predictedUpper : changed.omega receiver *
      (changed.predictedTime sectionTime count (receiver + 1) - changed.predictedTime sectionTime count source) ≤
      4 * changed.omega (receiver + 1) ^ changed.alpha / (changed.ratio ^ (1 - changed.alpha) - 1) := by
    rw [predictedDifference]
    have finite := Finset.sum_le_sum (fun index (_ : index ∈ Finset.Ico (receiver + 1) source) => delayUpper index)
    rw [← Finset.mul_sum] at finite
    have scaled := mul_le_mul_of_nonneg_left finite (omegaPositive receiver).le
    have kernel := scaled_delay_kernel_Ico_le changed frequencyPositive ratioGreaterOne alphaSmall
      receiver source (by omega)
    have bound := mul_le_mul_of_nonneg_left kernel (by norm_num : (0 : ℝ) ≤ 4)
    have firstBound : changed.omega receiver *
        (∑ index ∈ Finset.Ico (receiver + 1) source, changed.delay sectionTime index) ≤
        4 * (changed.omega receiver * (∑ index ∈ Finset.Ico (receiver + 1) source,
          changed.omega (index + 1) ^ changed.alpha / changed.omega index)) := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using scaled
    exact firstBound.trans (by simpa only [mul_div_assoc] using bound)
  have errorBound (index : ℕ) (ordered : receiver ≤ index) :
      changed.omega receiver * (timingError / changed.omega index) ≤ timingError := by
    have bound := mul_le_mul_of_nonneg_right (omegaMonotone ordered) timingErrorNonnegative
    have divided : changed.omega receiver * timingError / changed.omega index ≤ timingError :=
      (div_le_iff₀ (omegaPositive index)).mpr (by nlinarith only [bound])
    simpa only [mul_div_assoc] using divided
  have differenceUpper : changed.omega receiver * (actualTime (receiver + 1) - actualTime source) ≤
      changed.omega receiver * (changed.predictedTime sectionTime count (receiver + 1) -
        changed.predictedTime sectionTime count source) + 2 * timingError := by
    have first := (abs_le.mp receiverTiming).2
    have second := (abs_le.mp sourceTiming).1
    have difference : actualTime (receiver + 1) - actualTime source ≤
        changed.predictedTime sectionTime count (receiver + 1) - changed.predictedTime sectionTime count source +
          timingError / changed.omega (receiver + 1) + timingError / changed.omega source := by
      linarith only [first, second]
    have scaled := mul_le_mul_of_nonneg_left difference (omegaPositive receiver).le
    have firstError := errorBound (receiver + 1) (by omega)
    have secondError := errorBound source (by omega)
    nlinarith only [scaled, firstError, secondError]
  have extraErrors : 2 * timingError ≤
      4 * changed.omega (receiver + 1) ^ changed.alpha / (changed.ratio ^ (1 - changed.alpha) - 1) := by
    apply (le_div_iff₀ denominatorPositive).mpr
    have bound := timingSmall.trans (powerLarge (receiver + 1))
    nlinarith only [bound]
  refine ⟨sub_nonneg.mpr timeOrder, ?_⟩
  change changed.omega receiver * (actualTime (receiver + 1) - actualTime source) ≤
    8 * changed.omega (receiver + 1) ^ changed.alpha / (changed.ratio ^ (1 - changed.alpha) - 1)
  calc
    _ ≤ 4 * changed.omega (receiver + 1) ^ changed.alpha /
        (changed.ratio ^ (1 - changed.alpha) - 1) + 2 * timingError :=
      differenceUpper.trans (add_le_add_right predictedUpper _)
    _ ≤ 4 * changed.omega (receiver + 1) ^ changed.alpha /
        (changed.ratio ^ (1 - changed.alpha) - 1) +
        4 * changed.omega (receiver + 1) ^ changed.alpha /
          (changed.ratio ^ (1 - changed.alpha) - 1) := add_le_add_left extraErrors _
    _ = _ := by ring

end EulerNonuniqueness.Paper
