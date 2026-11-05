import EulerNonuniqueness.Section4.ReferenceContourClearance
import EulerNonuniqueness.Section1.IndividualPatchInteractionWeight

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem ReferenceCentroidFieldGeometry.local_source_center_gap
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {time : ℝ} {index : Fin count}
    (geometry : ReferenceCentroidFieldGeometry scales motion time index)
    (receiver : Fin 4) (source : Fin count) (patch : Fin 4)
    (different : (index, receiver) ≠ (source, patch)) :
    scales.individualInteractionDistance (index.val + 1) (source.val + 1) / 4 + 3 * scales.radius (source.val + 1) ≤
      ‖patchCentroid motion time index receiver - patchCentroid motion time source patch‖ := by
  by_cases same : source = index
  · subst source
    have patchDifferent : patch ≠ receiver := fun equality => different (by rw [equality])
    rw [Scales.individualInteractionDistance, if_pos rfl]
    linarith [geometry.internalSeparated receiver patch patchDifferent, geometry.internalRadius,
      scales.length_pos (index.val + 1)]
  · have member : source ∈ Finset.univ.erase index := Finset.mem_erase.mpr ⟨same, Finset.mem_univ _⟩
    have valuesDifferent : source.val + 1 ≠ index.val + 1 := fun equality => same (Fin.ext (Nat.add_right_cancel equality))
    rw [Scales.individualInteractionDistance, if_neg valuesDifferent]
    have lower := geometry.centroidsSeparated receiver source member patch
    have small := geometry.sourceSmall source member
    dsimp only [referenceSourceDistance] at lower small
    linarith

theorem ReferenceCentroidFieldGeometry.contour_center_gap_strict
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {time : ℝ} {index : Fin count}
    (geometry : ReferenceCentroidFieldGeometry scales motion time index)
    (receiver : Fin 4) (source : Fin count) (patch : Fin 4)
    (different : (index, receiver) ≠ (source, patch)) :
    scales.length (index.val + 1) / 400 + 3 * scales.radius (source.val + 1) <
      ‖patchCentroid motion time index receiver - patchCentroid motion time source patch‖ := by
  by_cases same : source = index
  · subst source
    have patchDifferent : patch ≠ receiver := fun equality => different (by rw [equality])
    linarith [geometry.internalSeparated receiver patch patchDifferent, geometry.internalRadius,
      scales.length_pos (index.val + 1)]
  · have member : source ∈ Finset.univ.erase index := Finset.mem_erase.mpr ⟨same, Finset.mem_univ _⟩
    linarith [geometry.centroidsSeparated receiver source member patch, geometry.sourceSmall source member,
      geometry.near source member, geometry.positive source member, scales.length_pos (index.val + 1)]

namespace FiniteMovingPatchFamily

theorem reference_local_source_clearance {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales) (time : ℝ) (index : Fin count)
    (radiusIdentity : ∀ source patch, (family.patch (finProdFinEquiv (source, patch))).radius = scales.radius (source.val + 1))
    (centerIdentity : ∀ source patch, (family.patch (finProdFinEquiv (source, patch))).center time =
      patchCentroid family.patchMotion time source patch)
    (geometry : ReferenceCentroidFieldGeometry scales family.patchMotion time index)
    (receiver : Fin 4) :
    (∀ source ∈ Finset.univ.erase (finProdFinEquiv (index, receiver)),
      scales.length (index.val + 1) / 400 + 3 * (family.patch source).radius <
        ‖(family.patch (finProdFinEquiv (index, receiver))).center time - (family.patch source).center time‖) ∧
    (∀ source ∈ Finset.univ.erase (finProdFinEquiv (index, receiver)),
      scales.individualInteractionDistance (index.val + 1) ((finProdFinEquiv.symm source).1.val + 1) / 4 +
        3 * (family.patch source).radius ≤
        ‖(family.patch (finProdFinEquiv (index, receiver))).center time - (family.patch source).center time‖) := by
  have pairDifferent (source : Fin (count * 4)) (member : source ∈ Finset.univ.erase (finProdFinEquiv (index, receiver))) :
      (index, receiver) ≠ finProdFinEquiv.symm source := by
    intro equality
    have applied := congrArg finProdFinEquiv equality
    simp only [Equiv.apply_symm_apply] at applied
    exact (Finset.mem_erase.mp member).1 applied.symm
  constructor
  · intro source member
    obtain ⟨⟨sourceIndex, sourcePatch⟩, equality⟩ := finProdFinEquiv.surjective source
    subst source
    have different := pairDifferent _ member
    simp only [Equiv.symm_apply_apply] at different
    rw [radiusIdentity, centerIdentity, centerIdentity]
    exact geometry.contour_center_gap_strict receiver sourceIndex sourcePatch different
  · intro source member
    obtain ⟨⟨sourceIndex, sourcePatch⟩, equality⟩ := finProdFinEquiv.surjective source
    subst source
    have different := pairDifferent _ member
    simp only [Equiv.symm_apply_apply] at different
    simp only [Equiv.symm_apply_apply]
    rw [radiusIdentity, centerIdentity, centerIdentity]
    exact geometry.local_source_center_gap receiver sourceIndex sourcePatch different

end FiniteMovingPatchFamily

end EulerNonuniqueness.Paper
