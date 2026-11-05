import EulerNonuniqueness.Section5.CascadeMaterialPreparedPair
import EulerNonuniqueness.Section4.UniversalReferenceMechanicalData

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_cascade_reference_sharp_defect_small (scales : Scales)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {referenceConstant tolerance : ℝ} (referenceNonnegative : 0 ≤ referenceConstant)
    (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop,
      ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
        {threshold scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ time ∈ Icc (0 : ℝ) 1, ∀ index : Fin count,
      |diagonalDifference prepared.reference time index /
          ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2 - 1| +
        |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| < tolerance := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (1 + 3 * referenceConstant / tolerance),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency frequencyOne frequencyLarge strainSmall
  intro orbit sectionTime phase dipoleAngle threshold scaleRoot shapeRadius factor monitor boundaryConstant count prepared time inside index
  let changed : Scales := {scales with frequency := frequency}
  let omega := changed.omega (index.val + 1)
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have omegaFrequency : frequency ≤ omega := changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith) _
  have omegaOne : 1 ≤ omega := frequencyOne.trans omegaFrequency
  have omegaPositive : 0 < omega := zero_lt_one.trans_le omegaOne
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  obtain ⟨unstable, lift, initial, phaseLift, evolution, coarse, sharp⟩ := prepared.referenceSolution
  have actual := (sharp.1 1 (by norm_num) le_rfl time inside index).1
  have defect : |diagonalDifference prepared.reference time index / changed.length (index.val + 1) ^ 2 - 1| +
      |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| ≤
      referenceConstant * ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5) := by
    simp only [one_mul] at actual
    linarith [abs_nonneg (angularImpulse changed prepared.reference time index /
      (2 * changed.circulation (index.val + 1) * changed.length (index.val + 1) ^ 2) - 1)]
  have strainBudget : changed.strain + changed.strain ^ 2 ≤ 2 := by nlinarith [strainSmall.le]
  have inverseBound : omega⁻¹ ^ 5 ≤ omega⁻¹ := by
    have inverseNonnegative : 0 ≤ omega⁻¹ := inv_nonneg.mpr omegaPositive.le
    have inverseOne : omega⁻¹ ≤ 1 := inv_le_one_of_one_le₀ omegaOne
    have power : omega⁻¹ ^ 4 ≤ 1 := pow_le_one₀ inverseNonnegative inverseOne
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right power inverseNonnegative).trans_eq (by ring)
  have envelope : (changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5 ≤ 3 / omega := by
    have first := div_le_div_of_nonneg_right strainBudget omegaPositive.le
    have sum := add_le_add first inverseBound
    exact sum.trans_eq (by rw [← one_div]; ring)
  have positiveSlack : 3 * referenceConstant < tolerance * omega := by
    have actual := (mul_le_mul_of_nonneg_left (frequencyLarge.trans omegaFrequency) tolerancePositive.le)
    have identity : tolerance * (1 + 3 * referenceConstant / tolerance) = tolerance + 3 * referenceConstant := by
      field_simp
      <;> ring
    rw [identity] at actual
    linarith
  have final : referenceConstant * (3 / omega) < tolerance := by
    have bound := (div_lt_iff₀ omegaPositive).mpr positiveSlack
    exact (by simpa only [mul_div_assoc, mul_comm] using bound)
  exact (defect.trans (mul_le_mul_of_nonneg_left envelope referenceNonnegative)).trans_lt final

end EulerNonuniqueness.Paper
