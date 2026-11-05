import EulerNonuniqueness.Section4.ReferenceCentroidFieldGeometry
import EulerNonuniqueness.Section3.FiniteMovingPatchMotion

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem ReferenceCentroidFieldGeometry.contour_center_gap
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {time : ℝ} {index : Fin count}
    (geometry : ReferenceCentroidFieldGeometry scales motion time index)
    (receiver : Fin 4) (source : Fin count) (patch : Fin 4)
    (different : (index, receiver) ≠ (source, patch)) :
    scales.length (index.val + 1) / 400 + 3 * scales.radius (source.val + 1) ≤
      ‖patchCentroid motion time index receiver - patchCentroid motion time source patch‖ := by
  by_cases same : source = index
  · subst source
    have patchDifferent : patch ≠ receiver := fun equality => different (by rw [equality])
    have actual := geometry.internalSeparated receiver patch patchDifferent
    have radiusBound := geometry.internalRadius
    linarith [scales.length_pos (index.val + 1)]
  · have member : source ∈ Finset.univ.erase index := Finset.mem_erase.mpr ⟨same, Finset.mem_univ _⟩
    have actual := geometry.centroidsSeparated receiver source member patch
    have radiusBound := geometry.sourceSmall source member
    have lengthBound := geometry.near source member
    have positive := geometry.positive source member
    linarith

namespace FiniteMovingPatchFamily

theorem reference_contour_center_gaps {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales) (time : ℝ) (index : Fin count)
    (radiusIdentity : ∀ source patch, (family.patch (finProdFinEquiv (source, patch))).radius = scales.radius (source.val + 1))
    (centerIdentity : ∀ source patch, (family.patch (finProdFinEquiv (source, patch))).center time =
      patchCentroid family.patchMotion time source patch)
    (geometry : ReferenceCentroidFieldGeometry scales family.patchMotion time index)
    (receiver : Fin 4) :
    ∀ source ∈ Finset.univ.erase (finProdFinEquiv (index, receiver)),
      scales.length (index.val + 1) / 400 + 3 * (family.patch source).radius ≤
        ‖(family.patch (finProdFinEquiv (index, receiver))).center time - (family.patch source).center time‖ := by
  intro source member
  obtain ⟨⟨sourceIndex, sourcePatch⟩, equality⟩ := finProdFinEquiv.surjective source
  subst source
  have different : (index, receiver) ≠ (sourceIndex, sourcePatch) := by
    intro equality
    exact (Finset.mem_erase.mp member).1 (congrArg finProdFinEquiv equality.symm)
  rw [radiusIdentity, centerIdentity, centerIdentity]
  exact geometry.contour_center_gap receiver sourceIndex sourcePatch different

end FiniteMovingPatchFamily

end EulerNonuniqueness.Paper
