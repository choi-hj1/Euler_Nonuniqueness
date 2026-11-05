import EulerNonuniqueness.Section6.MovingForeignQuadrupole
import EulerNonuniqueness.Section6.MovingPatchFamilyQuadrupole
import EulerNonuniqueness.General.WeightedFiniteCorrectionSeries
import EulerNonuniqueness.Section6.PaperRelativeNeutralPointSeries

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

namespace FiniteMovingPatchFamily

theorem exteriorTaylorCoefficient_foreign_eq_sum_quadrupoles {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (receiver : Fin count)
    (center : ℝ → ℂ) (radius : ℝ) (power : ℕ) (time : ℝ) :
    family.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver) center radius (power + 1) time =
      ∑ source ∈ Finset.univ.erase receiver,
        (family.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ center radius (power + 1) time := by
  rw [family.exteriorTaylorCoefficient_eq_sum_sourceTaylorCoefficient, foreignQuadrupolePatchLabels,
    Finset.sum_image (fun first _ second _ equality => finProdFinEquiv.injective equality)]
  simp only [Finset.product_eq_sprod]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro source _
  rw [(family.quadrupoleSubfamily source).exteriorTaylorCoefficient_eq_sum_sourceTaylorCoefficient]
  rfl

theorem exteriorTaylorCoefficient_foreign_eq_quadrupoleExteriorCoefficient {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ index patch, family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (receiver : Fin count) (radius time : ℝ) (power : ℕ) {distance : ℝ}
    (positive : 0 < distance)
    (separated : ∀ source ∈ Finset.univ.erase receiver, ∀ patch position,
      position ∈ family.patchMotion.domain time source patch →
        distance ≤ ‖quadrupoleCenter family.patchMotion time receiver - position‖) :
    family.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
      (fun current => quadrupoleCenter family.patchMotion current receiver) radius (power + 1) time =
        quadrupoleExteriorCoefficient scales family.patchMotion receiver time radius power := by
  have gap : ∀ source ∈ foreignQuadrupolePatchLabels receiver, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖quadrupoleCenter family.patchMotion time receiver - position‖ := by
    intro label member position inside
    obtain ⟨⟨source, patch⟩, rfl⟩ := finProdFinEquiv.surjective label
    exact separated source (Finset.mem_erase.mpr
      ⟨(mem_foreignQuadrupolePatchLabels receiver source patch).mp member, Finset.mem_univ source⟩) patch position inside
  have actual := family.exteriorTaylorCoefficient_eq_vorticityCoefficient (foreignQuadrupolePatchLabels receiver)
    (fun current => quadrupoleCenter family.patchMotion current receiver) radius time power positive gap
  have fields := family.externalPatchVorticity_eq_subfamily scales densityEquation time receiver
  have transported := congrArg (fun vorticity => Section6.exteriorVorticityCoefficient vorticity
    (quadrupoleCenter family.patchMotion time receiver) radius power) fields.symm
  exact actual.trans transported

end FiniteMovingPatchFamily

namespace MovingPatchFamilySourceComparison

theorem exteriorTaylorCoefficient_foreign_difference_eq_sum {count : ℕ}
    (comparison : MovingPatchFamilySourceComparison (count * 4)) (receiver : Fin count) (power : ℕ) :
    comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
        comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
      comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
        comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time =
      ∑ source ∈ Finset.univ.erase receiver,
        ((comparison.quadrupole source).first.exteriorTaylorCoefficient Finset.univ
            comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
          (comparison.quadrupole source).second.exteriorTaylorCoefficient Finset.univ
            comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time) := by
  rw [comparison.first.exteriorTaylorCoefficient_foreign_eq_sum_quadrupoles,
    comparison.second.exteriorTaylorCoefficient_foreign_eq_sum_quadrupoles, ← Finset.sum_sub_distrib]
  rfl

theorem exteriorTaylorCoefficient_foreign_weighted_difference_le_sum {count : ℕ}
    (comparison : MovingPatchFamilySourceComparison (count * 4)) (receiver : Fin count)
    {weight : ℝ} (weightNonnegative : 0 ≤ weight)
    (summable : ∀ source ∈ Finset.univ.erase receiver, Summable (fun power : ℕ => weight ^ (power + 1) *
      ‖(comparison.quadrupole source).first.exteriorTaylorCoefficient Finset.univ
          comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
        (comparison.quadrupole source).second.exteriorTaylorCoefficient Finset.univ
          comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖)) :
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
      ∑ source ∈ Finset.univ.erase receiver, ∑' power : ℕ, weight ^ (power + 1) *
        ‖(comparison.quadrupole source).first.exteriorTaylorCoefficient Finset.univ
            comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
          (comparison.quadrupole source).second.exteriorTaylorCoefficient Finset.univ
            comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖ := by
  have actual := EulerNonuniqueness.General.summable_weighted_norm_of_eq_add_finite_corrections
    (Finset.univ.erase receiver) (fun power => weight ^ (power + 1))
    (fun power => pow_nonneg weightNonnegative _) _ (fun _ => (0 : ℂ))
    (fun source power => (comparison.quadrupole source).first.exteriorTaylorCoefficient Finset.univ
      comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
        (comparison.quadrupole source).second.exteriorTaylorCoefficient Finset.univ
          comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time)
    (fun power => by simpa only [zero_add] using comparison.exteriorTaylorCoefficient_foreign_difference_eq_sum receiver power)
    (by simpa only [norm_zero, mul_zero] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))) summable
  simpa only [norm_zero, mul_zero, tsum_zero, zero_add] using actual

end MovingPatchFamilySourceComparison

end EulerNonuniqueness.Paper
