import EulerNonuniqueness.Section6.SourcePacketUniformReceiverPhaseRate
import EulerNonuniqueness.Section6.SourcePacketReceiverDiagonalSmallness
import EulerNonuniqueness.Section6.SourcePacketActualReceiverPhase
import EulerNonuniqueness.Section6.SourcePacketLocalPhaseKinematics

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000

theorem Scales.exists_eventually_actual_local_phase_drift (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {scaleRoot boundaryConstant tolerance : ℝ}
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
    (tolerancePositive : 0 < tolerance) :
    ∃ chartRadius > (0 : ℝ),
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant shapeRadius factor monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, threshold ≤ 1 / 2 → factor ≤ 1 / 8 →
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
    (∀ time ∈ Icc 0 finish, |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
      |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ chartRadius) →
    ∃ lift : ℝ → ℝ, Continuous lift ∧ lift 0 = phase (index.val + 1) ∧
      (∀ time ∈ Icc 0 finish, positiveHalfDiagonal prepared.trajectory.movingFamily.patchMotion time index =
        (‖positiveHalfDiagonal prepared.trajectory.movingFamily.patchMotion time index‖ : ℂ) *
          Complex.exp (Complex.I * (lift time : ℂ))) ∧
      ∀ start horizon : ℝ, 0 ≤ start → 0 ≤ horizon → start + horizon ≤ finish →
      ∀ elapsed ∈ Icc 0 horizon,
      |lift (start + elapsed) - lift start +
        ({scales with frequency := frequency} : Scales).omega (index.val + 1) * elapsed| ≤
        tolerance * ({scales with frequency := frequency} : Scales).omega (index.val + 1) * elapsed := by
  obtain ⟨constant, constantOne, phaseRadius, phaseRadiusPositive, rate⟩ :=
    scales.exists_eventually_actual_receiver_phase_rate amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative
  have constantPositive : 0 < constant := zero_lt_one.trans_le constantOne
  let chartRadius := min (1 / 4 : ℝ) (min (phaseRadius / 2) (tolerance / (4 * constant)))
  have chartPositive : 0 < chartRadius := by dsimp only [chartRadius]; positivity
  refine ⟨chartRadius, chartPositive, ?_⟩
  have forcingLimit := (scales.strain_tendsto_zero ratioBound alphaPositive).add
    ((tendsto_inv_atTop_zero : Tendsto (fun frequency : ℝ => frequency⁻¹) atTop (𝓝 0)).pow 4)
  simp only [add_zero, zero_pow (by norm_num : (4 : ℕ) ≠ 0)] at forcingLimit
  filter_upwards [eventually_ge_atTop (1 : ℝ), rate,
    scales.eventually_actual_receiver_diagonal_small amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative
      (show 0 < tolerance / 8 by positivity),
    scales.eventually_actual_receiver_phase_lift amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative,
    scales.eventually_rhombus_joint_diagonal_neutral_continuation amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative,
    forcingLimit.eventually (eventually_lt_nhds (show 0 < tolerance / (4 * constant) by positivity))]
    with frequency frequencyOne rate diagonal phases joint forcingSmall
  intro orbit sectionTime phase dipoleAngle threshold referenceConstant shapeRadius factor monitor count prepared path
    thresholdSmall factorSmall index nonterminal finish finishNonnegative finishBound radialSmall chartSmall
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have omegaFrequency := changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith) (index.val + 1)
  have omegaOne : 1 ≤ changed.omega (index.val + 1) := frequencyOne.trans omegaFrequency
  have omegaPositive : 0 < changed.omega (index.val + 1) := zero_lt_one.trans_le omegaOne
  obtain ⟨lift, continuous, initial, properties⟩ := phases prepared path thresholdSmall factorSmall index nonterminal
    finish finishNonnegative finishBound radialSmall
  refine ⟨lift, continuous, initial, fun time inside => (properties time inside).2, ?_⟩
  intro start horizon startNonnegative horizonNonnegative endBound elapsed inside
  have timeRange (current : ℝ) (member : current ∈ Icc 0 horizon) : start + current ∈ Icc 0 finish :=
    ⟨by linarith [member.1], by linarith [member.2]⟩
  have remainderBound (current : ℝ) (member : current ∈ Icc 0 horizon) :
      |referencePhaseError changed motion index (start + current)| ≤ changed.omega (index.val + 1) * (tolerance / 2) := by
    have chart := chartSmall (start + current) (timeRange current member)
    have chartQuarter := chart.trans (min_le_left _ _)
    have chartPhase : |unstableShape motion (start + current) index| + |stableShape motion (start + current) index| < phaseRadius :=
      lt_of_le_of_lt (chart.trans ((min_le_right _ _).trans (min_le_left _ _))) (by linarith)
    have actual := rate prepared path thresholdSmall factorSmall index nonterminal finish finishNonnegative finishBound radialSmall
      (start + current) (timeRange current member) chartQuarter chartPhase
    have chartBudget := chart.trans ((min_le_right _ _).trans (min_le_right _ _))
    have chartScaled := mul_le_mul_of_nonneg_left chartBudget (mul_nonneg constantPositive.le omegaPositive.le)
    have inverseBound := pow_le_pow_left₀ (inv_nonneg.mpr omegaPositive.le) (inv_anti₀ frequencyPositive omegaFrequency) 4
    have forceBudget : constant * (changed.strain + (changed.omega (index.val + 1))⁻¹ ^ 4) ≤ tolerance / 4 := by
      have small : changed.strain + (changed.omega (index.val + 1))⁻¹ ^ 4 ≤ tolerance / (4 * constant) :=
        (add_le_add_left inverseBound changed.strain).trans forcingSmall.le
      have multiplied := mul_le_mul_of_nonneg_left small constantPositive.le
      convert multiplied using 1 <;> field_simp [constantPositive.ne'] <;> ring
    have forceScaled := mul_le_mul_of_nonneg_left omegaOne (show 0 ≤ tolerance / 4 by positivity)
    have chartSimplified : constant * changed.omega (index.val + 1) *
        (|unstableShape motion (start + current) index| + |stableShape motion (start + current) index|) ≤
        changed.omega (index.val + 1) * tolerance / 4 := by
      convert chartScaled using 1 <;> field_simp [constantPositive.ne'] <;> ring
    nlinarith
  have localEstimate := source_packet_local_phase_increment_bound omegaPositive horizonNonnegative
    (show 0 ≤ tolerance / 8 by positivity) (show 0 ≤ tolerance / 2 by positivity)
    (phase := fun current => lift (start + current))
    (dilation := fun current => referenceDilation changed motion index (start + current))
    (remainder := fun current => referencePhaseError changed motion index (start + current))
    (fun current member => by
      simpa only [mul_one, Function.comp_def] using ((properties (start + current) (timeRange current member)).1.comp current
        ((hasDerivAt_id current).const_add start)))
    (fun current member => by
      have lower := (abs_le.mp (joint prepared path thresholdSmall factorSmall index nonterminal finish finishNonnegative
        finishBound radialSmall (start + current) (timeRange current member)).1).1
      change -(1 / 4 : ℝ) ≤ referenceDilation changed motion index (start + current) - 1 at lower
      linarith)
    (fun current member => diagonal prepared path thresholdSmall factorSmall index nonterminal finish finishNonnegative
      finishBound radialSmall (start + current) (timeRange current member)) remainderBound elapsed inside
  simp only [add_zero] at localEstimate
  exact localEstimate.trans (by nlinarith [mul_nonneg omegaPositive.le inside.1])

end EulerNonuniqueness.Paper
