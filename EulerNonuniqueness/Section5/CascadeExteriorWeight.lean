import EulerNonuniqueness.Section6.MovingEulerUniformExteriorWeight

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

theorem integral_inverseSquare_other_patches_le_scaled_uniform {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales) {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (inside : time ∈ Icc 0 horizon)
    (densityIdentity : ∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (factor : ℝ) (factorPositive : 0 < factor) (receiver : Fin (count * 4)) (center : ℂ)
    (separated : ∀ source ∈ Finset.univ.erase receiver, ∀ position ∈ (family.patch source).domain time,
      factor * scales.individualInteractionDistance ((finProdFinEquiv.symm receiver).1.val + 1)
        ((finProdFinEquiv.symm source).1.val + 1) ≤ ‖center - position‖) :
    (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase receiver) time) center position) ≤
      (80000 * Real.pi * scales.omega ((finProdFinEquiv.symm receiver).1.val + 1) +
        2304 * scales.strain) / factor ^ 2 := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  let distance := fun source : Fin (count * 4) =>
    scales.individualInteractionDistance ((finProdFinEquiv.symm receiver).1.val + 1)
      ((finProdFinEquiv.symm source).1.val + 1)
  have estimate := family.integral_inverseSquare_subfamily_le_circulations scales evolution inside densityIdentity
    amplitudePositive frequencyPositive ratioPositive (Finset.univ.erase receiver) center
    (fun source => factor * distance source)
    (fun source _ => mul_pos factorPositive (scales.individualInteractionDistance_pos _ _)) separated
  have sumBound :
      (∑ source ∈ Finset.univ.erase receiver,
        scales.circulation ((finProdFinEquiv.symm source).1.val + 1) / distance source ^ 2) ≤
      80000 * Real.pi * scales.omega ((finProdFinEquiv.symm receiver).1.val + 1) + 2304 * scales.strain := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_)
      (scales.sum_fourPatchInteractionWeight_le frequencyBound ratioBound alphaPositive (finProdFinEquiv.symm receiver).1)
    intro source _ _
    exact div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  apply estimate.trans
  calc
    (∑ source ∈ Finset.univ.erase receiver,
        scales.circulation ((finProdFinEquiv.symm source).1.val + 1) / (factor * distance source) ^ 2) =
      (∑ source ∈ Finset.univ.erase receiver,
        scales.circulation ((finProdFinEquiv.symm source).1.val + 1) / distance source ^ 2) / factor ^ 2 := by
      simp only [mul_pow, div_mul_eq_div_div, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro source member
      ring
    _ ≤ _ := div_le_div_of_nonneg_right sumBound (sq_nonneg factor)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
