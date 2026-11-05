import EulerNonuniqueness.Section6.MovingForeignCoefficientSum
import EulerNonuniqueness.General.ErasedAdjacentSum

noncomputable section

namespace EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison

theorem exteriorTaylorCoefficient_foreign_adjacent_weighted_difference_le
    {count : ℕ} (comparison : MovingPatchFamilySourceComparison (count * 4))
    (receiver adjacent : Fin count) (adjacentIdentity : receiver.val + 1 = adjacent.val)
    {weight : ℝ} (weightNonnegative : 0 ≤ weight)
    (summable : ∀ source ∈ Finset.univ.erase receiver, Summable (fun power : ℕ => weight ^ (power + 1) *
      ‖(comparison.quadrupole source).first.exteriorTaylorCoefficient Finset.univ
          comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
        (comparison.quadrupole source).second.exteriorTaylorCoefficient Finset.univ
          comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖)) :
    let sourceSeries := fun source => ∑' power : ℕ, weight ^ (power + 1) *
      ‖(comparison.quadrupole source).first.exteriorTaylorCoefficient Finset.univ
          comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
        (comparison.quadrupole source).second.exteriorTaylorCoefficient Finset.univ
          comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖
    Summable (fun power : ℕ => weight ^ (power + 1) *
      ‖comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
        comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖) ∧
    (∑' power : ℕ, weight ^ (power + 1) *
      ‖comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
        comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖) ≤
      (∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.val), sourceSeries source) +
        sourceSeries adjacent +
        ∑ source ∈ Finset.univ.filter (fun source : Fin count => receiver.val + 2 ≤ source.val), sourceSeries source := by
  dsimp only
  have actual := comparison.exteriorTaylorCoefficient_foreign_weighted_difference_le_sum receiver weightNonnegative summable
  refine ⟨actual.1, actual.2.trans_eq ?_⟩
  exact General.sum_erase_eq_lower_add_adjacent_add_finer receiver adjacent adjacentIdentity _

end EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison
