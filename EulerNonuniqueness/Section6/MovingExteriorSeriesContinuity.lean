import EulerNonuniqueness.Section6.FiniteExteriorWeightBound
import Mathlib.Analysis.NormedSpace.FunctionSeries

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

private theorem exists_uniform_subfamily_absolute_mass {count : ℕ}
    (family : FiniteMovingPatchFamily count) (selected : Finset (Fin count))
    {horizon : ℝ} (horizonNonnegative : 0 ≤ horizon) :
    ∃ mass ≥ (0 : ℝ), ∀ time ∈ Icc 0 horizon,
      (∫ position, |family.subfamilyVorticity selected time position|) ≤ mass := by
  obtain ⟨radius, _, domainBound⟩ := family.exists_uniform_domain_bound horizonNonnegative
  let majorant : ℂ → ℝ := (Metric.closedBall (0 : ℂ) radius).indicator
    (fun _ => ∑ source ∈ selected, |family.density source|)
  have majorantIntegrable : Integrable majorant :=
    memLp_one_iff_integrable.mp (memLp_indicator_const 1 measurableSet_closedBall _
      (Or.inr measure_closedBall_lt_top.ne))
  refine ⟨∫ position, majorant position, integral_nonneg (fun position =>
    indicator_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) position), ?_⟩
  intro time inside
  apply integral_mono (family.subfamilyVorticity_integrable selected time).norm majorantIntegrable
  intro position
  change |family.subfamilyVorticity selected time position| ≤ majorant position
  by_cases member : position ∈ Metric.closedBall (0 : ℂ) radius
  · simpa only [majorant, indicator_of_mem member] using family.abs_subfamilyVorticity_le selected time position
  · have outside (source : Fin count) : position ∉ (family.patch source).domain time :=
      fun sourceInside => member (domainBound time inside source sourceInside)
    simp only [subfamilyVorticity, patchVorticity, indicator_of_not_mem (outside _), Finset.sum_const_zero,
      abs_zero, majorant, indicator_of_not_mem member, le_refl]

private theorem norm_exteriorTaylorCoefficient_le_mass {count : ℕ}
    (family : FiniteMovingPatchFamily count) (selected : Finset (Fin count))
    (center : ℝ → ℂ) {radius distance mass time : ℝ}
    (radiusNonnegative : 0 ≤ radius) (distancePositive : 0 < distance)
    (separated : ∀ source ∈ selected, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖center time - position‖)
    (massBound : (∫ position, |family.subfamilyVorticity selected time position|) ≤ mass)
    (power : ℕ) :
    ‖family.exteriorTaylorCoefficient selected center radius (power + 1) time‖ ≤
      (radius / distance) ^ power * (distance⁻¹ ^ 2 * mass / (2 * Real.pi)) := by
  rw [family.exteriorTaylorCoefficient_eq_vorticityCoefficient selected center radius time power distancePositive separated]
  have supportSeparated := family.subfamily_support_separated selected (center time) time distance separated
  have weightBound := integral_inverseSquareVorticityWeight_le_mass
    (family.subfamilyVorticity_integrable selected time) (center time) distancePositive supportSeparated
  have uniformWeightBound := weightBound.trans (mul_le_mul_of_nonneg_left massBound (sq_nonneg _))
  exact (norm_exteriorVorticityCoefficient_le (family.subfamilyVorticity_integrable selected time)
    (center time) radiusNonnegative distancePositive supportSeparated power).trans
    (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right uniformWeightBound (by positivity))
      (pow_nonneg (div_nonneg radiusNonnegative distancePositive.le) power))

theorem continuousOn_weighted_exteriorTaylorCoefficient_difference_tsum
    {firstCount secondCount : ℕ}
    (first : FiniteMovingPatchFamily firstCount) (second : FiniteMovingPatchFamily secondCount)
    (firstSelected : Finset (Fin firstCount)) (secondSelected : Finset (Fin secondCount))
    (firstCenter secondCenter : ℝ → ℂ) {radius distance weight horizon : ℝ}
    (radiusNonnegative : 0 ≤ radius) (distancePositive : 0 < distance)
    (weightNonnegative : 0 ≤ weight) (horizonNonnegative : 0 ≤ horizon)
    (small : weight * radius / distance < 1)
    (firstSeparated : ∀ time ∈ Icc 0 horizon, ∀ source ∈ firstSelected,
      ∀ position ∈ (first.patch source).domain time, distance ≤ ‖firstCenter time - position‖)
    (secondSeparated : ∀ time ∈ Icc 0 horizon, ∀ source ∈ secondSelected,
      ∀ position ∈ (second.patch source).domain time, distance ≤ ‖secondCenter time - position‖)
    (coefficientContinuous : ∀ power : ℕ, ContinuousOn (fun time =>
      first.exteriorTaylorCoefficient firstSelected firstCenter radius (power + 1) time -
        second.exteriorTaylorCoefficient secondSelected secondCenter radius (power + 1) time) (Icc 0 horizon)) :
    let terms := fun (power : ℕ) (time : ℝ) => weight ^ (power + 1) *
      ‖first.exteriorTaylorCoefficient firstSelected firstCenter radius (power + 1) time -
        second.exteriorTaylorCoefficient secondSelected secondCenter radius (power + 1) time‖
    (∀ time ∈ Icc 0 horizon, Summable (fun power : ℕ => terms power time)) ∧
      TendstoUniformlyOn (fun count time => ∑ power ∈ Finset.range count, terms power time)
        (fun time => ∑' power : ℕ, terms power time) atTop (Icc 0 horizon) ∧
      ContinuousOn (fun time => ∑' power : ℕ, terms power time) (Icc 0 horizon) := by
  dsimp only
  let terms := fun (power : ℕ) (time : ℝ) => weight ^ (power + 1) *
    ‖first.exteriorTaylorCoefficient firstSelected firstCenter radius (power + 1) time -
      second.exteriorTaylorCoefficient secondSelected secondCenter radius (power + 1) time‖
  obtain ⟨firstMass, firstMassNonnegative, firstMassBound⟩ :=
    exists_uniform_subfamily_absolute_mass first firstSelected horizonNonnegative
  obtain ⟨secondMass, secondMassNonnegative, secondMassBound⟩ :=
    exists_uniform_subfamily_absolute_mass second secondSelected horizonNonnegative
  let quotient := weight * radius / distance
  let constant := weight * (distance⁻¹ ^ 2 * (firstMass + secondMass) / (2 * Real.pi))
  have quotientNonnegative : 0 ≤ quotient := by dsimp only [quotient]; positivity
  have termsNonnegative (power : ℕ) (time : ℝ) : 0 ≤ terms power time :=
    mul_nonneg (pow_nonneg weightNonnegative _) (norm_nonneg _)
  have geometricSummable : Summable (fun power : ℕ => quotient ^ power * constant) :=
    (summable_geometric_of_lt_one quotientNonnegative small).mul_right constant
  have majorant (power : ℕ) (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      terms power time ≤ quotient ^ power * constant := by
    have firstBound := norm_exteriorTaylorCoefficient_le_mass first firstSelected firstCenter radiusNonnegative
      distancePositive (firstSeparated time inside) (firstMassBound time inside) power
    have secondBound := norm_exteriorTaylorCoefficient_le_mass second secondSelected secondCenter radiusNonnegative
      distancePositive (secondSeparated time inside) (secondMassBound time inside) power
    calc
      terms power time ≤ weight ^ (power + 1) *
          (‖first.exteriorTaylorCoefficient firstSelected firstCenter radius (power + 1) time‖ +
            ‖second.exteriorTaylorCoefficient secondSelected secondCenter radius (power + 1) time‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (pow_nonneg weightNonnegative _)
      _ ≤ weight ^ (power + 1) *
          ((radius / distance) ^ power * (distance⁻¹ ^ 2 * firstMass / (2 * Real.pi)) +
            (radius / distance) ^ power * (distance⁻¹ ^ 2 * secondMass / (2 * Real.pi))) :=
        mul_le_mul_of_nonneg_left (add_le_add firstBound secondBound) (pow_nonneg weightNonnegative _)
      _ = quotient ^ power * constant := by
        dsimp only [quotient, constant]
        rw [show weight * radius / distance = weight * (radius / distance) by ring, mul_pow, pow_succ]
        ring
  have normMajorant (power : ℕ) (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      ‖terms power time‖ ≤ quotient ^ power * constant := by
    rw [Real.norm_eq_abs, abs_of_nonneg (termsNonnegative power time)]
    exact majorant power time inside
  have termsContinuous (power : ℕ) : ContinuousOn (terms power) (Icc 0 horizon) :=
    continuousOn_const.mul (coefficientContinuous power).norm
  exact ⟨fun time inside => Summable.of_nonneg_of_le (fun power => termsNonnegative power time)
      (fun power => majorant power time inside) geometricSummable,
    tendstoUniformlyOn_tsum_nat geometricSummable normMajorant,
    continuousOn_tsum termsContinuous geometricSummable normMajorant⟩

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
