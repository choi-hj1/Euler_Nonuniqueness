import EulerNonuniqueness.Section6.SourcePacketPhaseRobustTail

noncomputable section

namespace EulerNonuniqueness.Section6

theorem rotatingRhombusGrowingStrainInput_phase_decomposition {radius : ℝ}
    (radiusNonzero : radius ≠ 0) (frequency circulation distance bearing receiverPhase outgoingPhase time : ℝ)
    (frequencyPositive : 0 < frequency) (distancePositive : 0 < distance) :
    let seed := Real.sqrt 3 * circulation ^ 2 /
      (2 * Real.sqrt 2 * Real.pi ^ 2 * frequency ^ 2 * distance ^ 4)
    let residual := 4 * bearing - 2 * receiverPhase - 2 * outgoingPhase + Real.arctan (1 / Real.sqrt 2) - Real.pi
    rotatingRhombusGrowingStrainInput radius frequency circulation distance bearing receiverPhase outgoingPhase time =
      Real.cos residual * idealGrowingInput frequency seed time +
        Real.sin residual * idealQuadratureInput frequency seed time := by
  let amplitude := 3 * circulation ^ 2 / (Real.pi ^ 2 * distance ^ 4)
  let target := Real.pi - Real.arctan (1 / Real.sqrt 2)
  let seed := Real.sqrt 3 * circulation ^ 2 /
    (2 * Real.sqrt 2 * Real.pi ^ 2 * frequency ^ 2 * distance ^ 4)
  have coefficientIdentity : amplitude * Real.sqrt 2 / (4 * Real.sqrt 3 * frequency ^ 2) = seed := by
    have direct := ideal_strain_source_coefficient frequency circulation distance target frequencyPositive distancePositive
    have phaseZero : target + Real.arctan (1 / Real.sqrt 2) - Real.pi = 0 := by dsimp only [target]; ring
    rw [phaseZero, Real.cos_zero, mul_one] at direct
    have normalized := idealStrainInput_weighted_integral frequency amplitude 0 frequencyPositive
    simp only [add_zero, Real.cos_zero, mul_one] at normalized
    exact normalized.symm.trans direct
  let residual := 4 * bearing - 2 * receiverPhase - 2 * outgoingPhase + Real.arctan (1 / Real.sqrt 2) - Real.pi
  have phaseIdentity : target + residual = 4 * bearing - 2 * receiverPhase - 2 * outgoingPhase := by
    dsimp only [target, residual]
    ring
  have decomposition := idealStrainInput_phase_decomposition frequency amplitude residual time frequencyPositive.ne'
  rw [show Real.pi - Real.arctan (1 / Real.sqrt 2) + residual = target + residual by rfl,
    phaseIdentity, coefficientIdentity] at decomposition
  rw [rotatingRhombusGrowingStrainInput_eq radiusNonzero]
  exact decomposition

theorem cos_lower_of_wrapped_phase_bound {residual tolerance : ℝ} (winding : ℤ)
    (toleranceNonnegative : 0 ≤ tolerance)
    (bounded : |residual - (winding : ℝ) * (2 * Real.pi)| ≤ tolerance) :
    1 - tolerance ^ 2 / 2 ≤ Real.cos residual := by
  have square := (sq_le_sq₀ (abs_nonneg (residual - (winding : ℝ) * (2 * Real.pi))) toleranceNonnegative).mpr bounded
  rw [sq_abs] at square
  have cosine := Real.one_sub_sq_div_two_le_cos (x := residual - (winding : ℝ) * (2 * Real.pi))
  rw [Real.cos_sub_int_mul_two_pi] at cosine
  linarith only [square, cosine]

end EulerNonuniqueness.Section6
