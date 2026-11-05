import EulerNonuniqueness.Section4.UniversalPaperReferenceSharpBounds
import EulerNonuniqueness.Section4.UniversalReferencePhaseLift
import EulerNonuniqueness.Section6.SourcePacketActualPhaseCost

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000

theorem exists_source_packet_reference_recipient :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ bound ≥ (0 : ℝ), bound ≤ scales.amplitude → ∀ threshold ≤ radius,
    ∀ chartTolerance phaseTolerance : ℝ, 0 < chartTolerance → 0 < phaseTolerance →
    ∀ᶠ frequency : ℝ in atTop, ∀ {count : ℕ} {phase : Fin count → ℝ},
    ∀ witness : ReferenceMaterialCoarseWitness {scales with frequency := frequency} phase threshold bound,
    ∀ time ∈ Icc (0 : ℝ) 1, ∀ index : Fin count,
    let motion := witness.trajectory.movingFamily.patchMotion
    let positive := positiveHalfDiagonal motion time index
    let negative := negativeHalfDiagonal motion time index
    let ideal := Complex.exp (Complex.I * ((phase index - ({scales with frequency := frequency} : Scales).omega (index.val + 1) * time : ℝ) : ℂ))
    positive ≠ 0 ∧ negative ≠ 0 ∧
      |(pointShapeChart positive negative).1| + |(pointShapeChart positive negative).2| ≤ chartTolerance ∧
      ‖star positive / positive - star ideal / ideal‖ ≤ phaseTolerance := by
  obtain ⟨radius, radiusPositive, radiusSmall, constant, constantOne, sharp⟩ := exists_uniform_paper_reference_sharp_bounds
  refine ⟨radius, radiusPositive, radiusSmall, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive bound boundNonnegative amplitudeBound threshold thresholdBound
    chartTolerance phaseTolerance chartPositive phasePositive
  have constantPositive : 0 < constant := zero_lt_one.trans_le constantOne
  let tolerance := min (1 / 4 : ℝ) (min chartTolerance (phaseTolerance / 2))
  have tolerancePositive : 0 < tolerance := by dsimp only [tolerance]; positivity
  have inverseLimit := (tendsto_inv_atTop_zero : Tendsto (fun frequency : ℝ => frequency⁻¹) atTop (𝓝 0)).pow 4
  have totalLimit := (((scales.strain_tendsto_zero ratioBound alphaPositive).add
    ((scales.strain_tendsto_zero ratioBound alphaPositive).pow 2)).add inverseLimit).const_mul constant
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_pow (by norm_num : (4 : ℕ) ≠ 0), add_zero, mul_zero] at totalLimit
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    sharp scales amplitudePositive ratioBound alphaPositive bound boundNonnegative amplitudeBound threshold thresholdBound,
    scales.eventually_reference_phaseLift_of_coarse amplitudePositive ratioBound alphaPositive
      (thresholdBound.trans radiusSmall) boundNonnegative,
    totalLimit.eventually (eventually_lt_nhds tolerancePositive)]
    with frequency frequencyOne sharp lifted totalSmall
  intro count phase witness time inside index
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let motion := witness.trajectory.movingFamily.patchMotion
  let positive := positiveHalfDiagonal motion time index
  let negative := negativeHalfDiagonal motion time index
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have omegaFrequency := changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith) (index.val + 1)
  have omegaOne : 1 ≤ changed.omega (index.val + 1) := frequencyOne.trans omegaFrequency
  have omegaPositive : 0 < changed.omega (index.val + 1) := zero_lt_one.trans_le omegaOne
  have inverseNonnegative : 0 ≤ (changed.omega (index.val + 1))⁻¹ := inv_nonneg.mpr omegaPositive.le
  have inverseOne : (changed.omega (index.val + 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ omegaOne
  have inverseBound := pow_le_pow_left₀ inverseNonnegative (inv_anti₀ frequencyPositive omegaFrequency) 4
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive (by change 0 < scales.ratio; linarith) _).le (sq_nonneg _)
  obtain ⟨lift, liftProperties⟩ := lifted motion witness.initial witness.evolution witness.coarse
  have estimates := sharp motion witness.evolution lift witness.initial liftProperties witness.coarse 1 (by norm_num)
    le_rfl time inside index
  have commonSmall : constant * (changed.strain + changed.strain ^ 2 + (changed.omega (index.val + 1))⁻¹ ^ 4) ≤ tolerance := by
    have bound := mul_le_mul_of_nonneg_left (add_le_add_left inverseBound (changed.strain + changed.strain ^ 2)) constantPositive.le
    exact bound.trans totalSmall.le
  have shapeSmall : |unstableShape motion time index| + |stableShape motion time index| ≤ tolerance := by
    have division := div_le_self (show 0 ≤ changed.strain + changed.strain ^ 2 by positivity) omegaOne
    have power := mul_le_mul_of_nonneg_left inverseOne (pow_nonneg inverseNonnegative 4)
    have powerBound : (changed.omega (index.val + 1))⁻¹ ^ 5 ≤ (changed.omega (index.val + 1))⁻¹ ^ 4 := by
      calc
        _ = (changed.omega (index.val + 1))⁻¹ ^ 4 * (changed.omega (index.val + 1))⁻¹ := by ring
        _ ≤ _ := by simpa only [mul_one] using power
    have numeric : constant * ((changed.strain + changed.strain ^ 2) / changed.omega (index.val + 1) +
        (changed.omega (index.val + 1))⁻¹ ^ 5) ≤
        constant * (changed.strain + changed.strain ^ 2 + (changed.omega (index.val + 1))⁻¹ ^ 4) := by
      apply mul_le_mul_of_nonneg_left _ constantPositive.le
      exact add_le_add division powerBound
    have actual := estimates.1
    simp only [one_mul] at actual
    have impulseNonnegative := abs_nonneg (angularImpulse changed motion time index /
      (2 * changed.circulation (index.val + 1) * changed.length (index.val + 1) ^ 2) - 1)
    have diagonalNonnegative := abs_nonneg (diagonalDifference motion time index / changed.length (index.val + 1) ^ 2 - 1)
    have shape := (numeric.trans commonSmall)
    linarith
  have chartQuarter := shapeSmall.trans (min_le_left _ _)
  have chartIdentity : pointShapeChart positive negative = (unstableShape motion time index, stableShape motion time index) :=
    pointShapeChart_eq_paper_shape_of_upper motion time index (paper_shape_ratio_im_pos_of_small motion time index chartQuarter)
  have coherentSmall : |(pointShapeChart positive negative).1| + |(pointShapeChart positive negative).2| ≤ 1 / 4 := by
    simpa only [chartIdentity] using chartQuarter
  obtain ⟨positiveNonzero, negativeNonzero, _, _⟩ := pointShapeChart_reference_annulus positive negative coherentSmall
  refine ⟨positiveNonzero, negativeNonzero, ?_, ?_⟩
  · rw [chartIdentity]
    exact shapeSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  · have polar := (liftProperties index).2.2 time ⟨inside.1, inside.2.trans (by norm_num)⟩
    have idealPolar := conjugate_ratio_rotated_radius (by norm_num : (1 : ℝ) ≠ 0)
      (phase index - changed.omega (index.val + 1) * time)
    simp only [Complex.ofReal_one, one_mul] at idealPolar
    rw [source_packet_polar_conjugate_ratio positiveNonzero polar, idealPolar]
    have comparison := source_packet_phase_exponential_difference (lift time index)
      (phase index - changed.omega (index.val + 1) * time)
    have phaseBound := estimates.2
    simp only [one_mul, mul_one] at phaseBound
    have identity : lift time index - (phase index - changed.omega (index.val + 1) * time) =
        lift time index - phase index + changed.omega (index.val + 1) * time := by ring
    rw [identity] at comparison
    have total := phaseBound.trans commonSmall
    have toleranceBound := (min_le_right (1 / 4 : ℝ) (min chartTolerance (phaseTolerance / 2))).trans (min_le_right _ _)
    exact comparison.trans (by nlinarith)

end EulerNonuniqueness.Paper
