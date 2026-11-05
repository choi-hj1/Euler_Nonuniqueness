import EulerNonuniqueness.Section6.MovingEulerExteriorWeightBound
import EulerNonuniqueness.Section1.IndividualPatchInteractionSum

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

theorem integral_inverseSquare_other_patches_le_uniform {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales) {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (inside : time ∈ Icc 0 horizon)
    (densityIdentity : ∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (receiver : Fin (count * 4)) (center : ℂ)
    (separated : ∀ source ∈ Finset.univ.erase receiver, ∀ position ∈ (family.patch source).domain time,
      scales.individualInteractionDistance ((finProdFinEquiv.symm receiver).1.val + 1)
        ((finProdFinEquiv.symm source).1.val + 1) ≤ ‖center - position‖) :
    (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase receiver) time) center position) ≤
      80000 * Real.pi * scales.omega ((finProdFinEquiv.symm receiver).1.val + 1) + 2304 * scales.strain := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have estimate := family.integral_inverseSquare_subfamily_le_circulations scales evolution inside densityIdentity
    amplitudePositive frequencyPositive ratioPositive (Finset.univ.erase receiver) center
    (fun source => scales.individualInteractionDistance ((finProdFinEquiv.symm receiver).1.val + 1)
      ((finProdFinEquiv.symm source).1.val + 1))
    (fun source _ => scales.individualInteractionDistance_pos _ _) separated
  apply estimate.trans
  apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_)
    (scales.sum_fourPatchInteractionWeight_le frequencyBound ratioBound alphaPositive (finProdFinEquiv.symm receiver).1)
  intro source _ _
  exact div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
