import EulerNonuniqueness.Section6.MovingForeignCoefficientSum

noncomputable section

namespace EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison

theorem exteriorTaylorCoefficient_difference_eq_own_and_foreign {count : ℕ}
    (comparison : MovingPatchFamilySourceComparison (count * 4))
    (receiver : Fin count × Fin 4) (power : ℕ) :
    comparison.first.exteriorTaylorCoefficient (Finset.univ.erase (finProdFinEquiv receiver))
        comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
      comparison.second.exteriorTaylorCoefficient (Finset.univ.erase (finProdFinEquiv receiver))
        comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time =
      ((comparison.quadrupole receiver.1).first.exteriorTaylorCoefficient (Finset.univ.erase receiver.2)
          comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
        (comparison.quadrupole receiver.1).second.exteriorTaylorCoefficient (Finset.univ.erase receiver.2)
          comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time) +
      (comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
          comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
        comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
          comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time) := by
  rw [comparison.exteriorTaylorCoefficient_difference_eq_own_and_foreign_quadrupoles receiver power,
    comparison.exteriorTaylorCoefficient_foreign_difference_eq_sum receiver.1 power]

theorem exteriorTaylorCoefficient_erased_weighted_difference_le_own_foreign {count : ℕ}
    (comparison : MovingPatchFamilySourceComparison (count * 4))
    (receiver : Fin count × Fin 4) {weight : ℝ} (weightNonnegative : 0 ≤ weight)
    (ownSummable : Summable (fun power : ℕ => weight ^ (power + 1) *
      ‖(comparison.quadrupole receiver.1).first.exteriorTaylorCoefficient (Finset.univ.erase receiver.2)
          comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
        (comparison.quadrupole receiver.1).second.exteriorTaylorCoefficient (Finset.univ.erase receiver.2)
          comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖))
    (foreignSummable : Summable (fun power : ℕ => weight ^ (power + 1) *
      ‖comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
          comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
        comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
          comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖)) :
    Summable (fun power : ℕ => weight ^ (power + 1) *
      ‖comparison.first.exteriorTaylorCoefficient (Finset.univ.erase (finProdFinEquiv receiver))
          comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
        comparison.second.exteriorTaylorCoefficient (Finset.univ.erase (finProdFinEquiv receiver))
          comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖) ∧
    (∑' power : ℕ, weight ^ (power + 1) *
      ‖comparison.first.exteriorTaylorCoefficient (Finset.univ.erase (finProdFinEquiv receiver))
          comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
        comparison.second.exteriorTaylorCoefficient (Finset.univ.erase (finProdFinEquiv receiver))
          comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖) ≤
      (∑' power : ℕ, weight ^ (power + 1) *
        ‖(comparison.quadrupole receiver.1).first.exteriorTaylorCoefficient (Finset.univ.erase receiver.2)
            comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
          (comparison.quadrupole receiver.1).second.exteriorTaylorCoefficient (Finset.univ.erase receiver.2)
            comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖) +
      ∑' power : ℕ, weight ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
            comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
          comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
            comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖ := by
  have bound (power : ℕ) :
      weight ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient (Finset.univ.erase (finProdFinEquiv receiver))
            comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
          comparison.second.exteriorTaylorCoefficient (Finset.univ.erase (finProdFinEquiv receiver))
            comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖ ≤
      weight ^ (power + 1) *
        ‖(comparison.quadrupole receiver.1).first.exteriorTaylorCoefficient (Finset.univ.erase receiver.2)
            comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
          (comparison.quadrupole receiver.1).second.exteriorTaylorCoefficient (Finset.univ.erase receiver.2)
            comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖ +
      weight ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
            comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
          comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
            comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖ := by
    rw [comparison.exteriorTaylorCoefficient_difference_eq_own_and_foreign receiver power, ← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (pow_nonneg weightNonnegative _)
  have majorant := ownSummable.add foreignSummable
  have actualSummable := Summable.of_nonneg_of_le
    (fun power => mul_nonneg (pow_nonneg weightNonnegative (power + 1)) (norm_nonneg _)) bound majorant
  refine ⟨actualSummable, ?_⟩
  have estimate := actualSummable.tsum_le_tsum bound majorant
  rw [ownSummable.tsum_add foreignSummable] at estimate
  exact estimate

end EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison
