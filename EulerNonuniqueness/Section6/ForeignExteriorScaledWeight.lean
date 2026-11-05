import EulerNonuniqueness.Section6.MovingForeignQuadrupole

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 4000000

theorem external_inverseSquare_weight_le_scaled_strain {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales) {horizon time clearance : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (inside : time ∈ Icc 0 horizon)
    (densityEquation : ∀ index patch, family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (clearancePositive : 0 < clearance) (receiver : Fin count) (center : ℂ)
    (separated : ∀ source ∈ foreignQuadrupolePatchLabels receiver,
      ∀ position ∈ (family.patch source).domain time,
        clearance * (|scales.location (receiver.val + 1) -
          scales.location ((finProdFinEquiv.symm source).1.val + 1)| / 8) ≤ ‖center - position‖) :
    (∫ position, Section6.inverseSquareVorticityWeight
      (family.subfamilyVorticity (foreignQuadrupolePatchLabels receiver) time) center position) ≤
      2304 * scales.strain / clearance ^ 2 := by
  let distance := fun label : Fin (count * 4) =>
    |scales.location (receiver.val + 1) - scales.location ((finProdFinEquiv.symm label).1.val + 1)| / 8
  have positive (label : Fin (count * 4)) (member : label ∈ foreignQuadrupolePatchLabels receiver) :
      0 < distance label := by
    obtain ⟨⟨source, patch⟩, rfl⟩ := finProdFinEquiv.surjective label
    have different := (mem_foreignQuadrupolePatchLabels receiver source patch).mp member
    apply div_pos _ (by norm_num)
    apply scales.location_distance_pos
    simpa only [Equiv.symm_apply_apply] using
      (show receiver.val + 1 ≠ source.val + 1 from fun equality =>
        different (Fin.ext (Nat.add_right_cancel equality).symm))
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have actual := family.integral_inverseSquare_subfamily_le_circulations scales evolution inside densityEquation
    amplitudePositive frequencyPositive ratioPositive (foreignQuadrupolePatchLabels receiver) center
    (fun label => clearance * distance label) (fun label member => mul_pos clearancePositive (positive label member)) separated
  have identity : (∑ label ∈ foreignQuadrupolePatchLabels receiver,
      scales.circulation ((finProdFinEquiv.symm label).1.val + 1) / (clearance * distance label) ^ 2) =
      clearance⁻¹ ^ 2 * ∑ label ∈ foreignQuadrupolePatchLabels receiver,
        scales.circulation ((finProdFinEquiv.symm label).1.val + 1) / distance label ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro label _
    simp only [mul_pow, div_eq_mul_inv, inv_mul_cancel₀, mul_inv_rev]
    ring
  rw [identity] at actual
  have unscaled : (∑ label ∈ foreignQuadrupolePatchLabels receiver,
      scales.circulation ((finProdFinEquiv.symm label).1.val + 1) / distance label ^ 2) ≤
      2304 * scales.strain := by
    change (∑ label ∈ foreignQuadrupolePatchLabels receiver,
      (fun source : Fin count => scales.circulation (source.val + 1) /
        (|scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 8) ^ 2)
        (finProdFinEquiv.symm label).1) ≤ _
    rw [sum_foreignQuadrupolePatchLabels receiver (fun source : Fin count => scales.circulation (source.val + 1) /
      (|scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 8) ^ 2)]
    have finiteBound := mul_le_mul_of_nonneg_left
      (scales.sum_foreignInteractionWeight_le frequencyBound ratioBound alphaPositive receiver 2)
      (by norm_num : (0 : ℝ) ≤ 4)
    exact finiteBound.trans_eq (by unfold Scales.strain; norm_num; ring)
  apply actual.trans
  convert mul_le_mul_of_nonneg_left unscaled (sq_nonneg clearance⁻¹) using 1 <;> ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
