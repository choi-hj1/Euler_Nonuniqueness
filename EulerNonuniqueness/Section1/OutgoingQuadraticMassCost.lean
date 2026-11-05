import EulerNonuniqueness.Section1.Scales

noncomputable section

namespace EulerNonuniqueness.Paper

theorem Scales.outgoing_arbitrary_weight_cost_le_quadratic_mass (scales : Scales) (source : ℕ)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {weight distance initialDistance neutral moment : ℝ}
    (weightPositive : 0 < weight) (weightSmall : weight ≤ scales.omega source)
    (distancePositive : 0 < distance) (distanceOne : distance ≤ 1)
    (initialNonnegative : 0 ≤ initialDistance) (momentNonnegative : 0 ≤ moment)
    (neutralBound : neutral ≤ scales.length source ^ 2 +
      scales.length source ^ 2 / (4 * scales.location source) * moment) :
    scales.circulation source ^ 2 / (weight ^ 2 * distance ^ 4) +
      (1 + initialDistance) * scales.circulation source * scales.length source ^ 2 / (weight * distance ^ 4) +
      scales.circulation source * neutral / (weight * distance ^ 3) ≤
      4 * (1 + initialDistance + moment) * (1 + (scales.location source)⁻¹) *
        (scales.circulation source ^ 2 / (weight ^ 2 * distance ^ 4)) := by
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive source
  have lengthPositive := scales.length_pos source
  have locationPositive := scales.location_pos source
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive source
  let base := scales.circulation source ^ 2 / (weight ^ 2 * distance ^ 4)
  let unit := scales.circulation source * scales.length source ^ 2 / (weight * distance ^ 4)
  have baseNonnegative : 0 ≤ base := by dsimp only [base]; positivity
  have unitNonnegative : 0 ≤ unit := by dsimp only [unit]; positivity
  have inverseNonnegative : 0 ≤ (scales.location source)⁻¹ := inv_nonneg.mpr locationPositive.le
  have unitIdentity : unit = (weight / (2 * Real.pi * scales.omega source)) * base := by
    dsimp only [unit, base]
    simp only [Scales.circulation]
    field_simp
    ring
  have ratioOne : weight / (2 * Real.pi * scales.omega source) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 2 * Real.pi * scales.omega source)).mpr
    have multiple := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 * Real.pi by linarith [Real.pi_gt_three]) omegaPositive.le
    linarith only [weightSmall, multiple]
  have unitBound : unit ≤ base := by
    rw [unitIdentity]
    exact mul_le_of_le_one_left baseNonnegative ratioOne
  have fractionBound : distance / (4 * scales.location source) ≤ (scales.location source)⁻¹ := by
    calc
      _ ≤ 4 / (4 * scales.location source) :=
        div_le_div_of_nonneg_right (by linarith only [distanceOne]) (by positivity)
      _ = _ := by field_simp
  have neutralComparison : scales.circulation source * neutral / (weight * distance ^ 3) ≤
      unit * (1 + (scales.location source)⁻¹ * moment) := by
    calc
      _ ≤ scales.circulation source * (scales.length source ^ 2 +
          scales.length source ^ 2 / (4 * scales.location source) * moment) / (weight * distance ^ 3) := by gcongr
      _ = unit * (distance + distance / (4 * scales.location source) * moment) := by
        dsimp only [unit]
        field_simp
        ring
      _ ≤ unit * (1 + (scales.location source)⁻¹ * moment) := by
        exact mul_le_mul_of_nonneg_left (add_le_add distanceOne
          (mul_le_mul_of_nonneg_right fractionBound momentNonnegative)) unitNonnegative
  have coefficientBound : 3 + initialDistance + (scales.location source)⁻¹ * moment ≤
      4 * (1 + initialDistance + moment) * (1 + (scales.location source)⁻¹) := by
    nlinarith only [initialNonnegative, momentNonnegative, inverseNonnegative,
      mul_nonneg initialNonnegative inverseNonnegative, mul_nonneg momentNonnegative inverseNonnegative]
  change base + (1 + initialDistance) * scales.circulation source * scales.length source ^ 2 /
    (weight * distance ^ 4) + scales.circulation source * neutral / (weight * distance ^ 3) ≤ _
  calc
    _ = base + (1 + initialDistance) * unit + scales.circulation source * neutral / (weight * distance ^ 3) := by
      dsimp only [unit]
      ring
    _ ≤ base + (1 + initialDistance) * unit + unit * (1 + (scales.location source)⁻¹ * moment) :=
      add_le_add_left neutralComparison _
    _ ≤ base + (1 + initialDistance) * base + base * (1 + (scales.location source)⁻¹ * moment) := by gcongr
    _ = base * (3 + initialDistance + (scales.location source)⁻¹ * moment) := by ring
    _ ≤ base * (4 * (1 + initialDistance + moment) * (1 + (scales.location source)⁻¹)) :=
      mul_le_mul_of_nonneg_left coefficientBound baseNonnegative
    _ = _ := by ring

end EulerNonuniqueness.Paper
