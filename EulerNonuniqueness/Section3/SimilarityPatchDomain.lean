import EulerNonuniqueness.Section3.AffinePatchDomain
import Mathlib.Analysis.Complex.Isometry

noncomputable section

open Set MeasureTheory
open scoped Pointwise

namespace EulerNonuniqueness.Paper

def similarityPatchDomain (center : ℂ) (radius : ℝ) (phase : Circle)
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3) : Set ℂ :=
  (fun position => center + radius • ((phase : ℂ) * position)) '' nearCircleInterior data small

def contourSimilarityHomeomorph (center : ℂ) {radius : ℝ} (radiusPositive : 0 < radius)
    (phase : Circle) : ℂ ≃ₜ ℂ :=
  (rotation phase).toHomeomorph.trans (contourAffineHomeomorph center radiusPositive)

theorem contourSimilarityHomeomorph_apply (center : ℂ) {radius : ℝ}
    (radiusPositive : 0 < radius) (phase : Circle) (position : ℂ) :
    contourSimilarityHomeomorph center radiusPositive phase position =
      center + radius • ((phase : ℂ) * position) := rfl

theorem similarityPatchDomain_isOpen (center : ℂ) {radius : ℝ} (radiusPositive : 0 < radius)
    (phase : Circle) (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    IsOpen (similarityPatchDomain center radius phase data small) :=
  (contourSimilarityHomeomorph center radiusPositive phase).isOpenMap _ (nearCircleInterior_isOpen data small)

theorem similarityPatchDomain_isBounded (center : ℂ) {radius : ℝ} (radiusPositive : 0 < radius)
    (phase : Circle) (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    Bornology.IsBounded (similarityPatchDomain center radius phase data small) := by
  have compactImage := (nearCircleInterior_isBounded data small).isCompact_closure.image
    (contourSimilarityHomeomorph center radiusPositive phase).continuous
  exact compactImage.isBounded.subset (image_mono subset_closure)

theorem similarityPatchDomain_frontier (center : ℂ) {radius : ℝ} (radiusPositive : 0 < radius)
    (phase : Circle) (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    frontier (similarityPatchDomain center radius phase data small) =
      range (fun label => center + radius • ((phase : ℂ) * data.val.1 label)) := by
  change frontier ((contourSimilarityHomeomorph center radiusPositive phase) '' nearCircleInterior data small) = _
  rw [← Homeomorph.image_frontier, nearCircleInterior_frontier data small, ← Set.range_comp]
  rfl

theorem integral_similarityPatchDomain {value : Type*} [NormedAddCommGroup value] [NormedSpace ℝ value]
    (center : ℂ) {radius : ℝ} (radiusPositive : 0 < radius) (phase : Circle)
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3) (function : ℂ → value) :
    (∫ position in similarityPatchDomain center radius phase data small, function position) =
      radius ^ 2 • (∫ position in nearCircleInterior data small,
        function (center + radius • ((phase : ℂ) * position))) := by
  let rotated := (rotation phase) '' nearCircleInterior data small
  have imageIdentity : similarityPatchDomain center radius phase data small =
      (fun position : ℂ => center + position) '' (radius • rotated) := by
    rw [similarityPatchDomain, ← Set.image_smul, Set.image_image]
    dsimp only [rotated]
    rw [Set.image_image]
    rfl
  have translation := (measurePreserving_add_left (volume : Measure ℂ) center).setIntegral_image_emb
    (Homeomorph.addLeft center).toMeasurableEquiv.measurableEmbedding function (radius • rotated)
  have scaling := Measure.setIntegral_comp_smul_of_pos (volume : Measure ℂ)
    (fun position => function (center + position)) rotated radiusPositive
  rw [Complex.finrank_real_complex] at scaling
  have multiplied := congrArg (fun result : value => radius ^ 2 • result) scaling
  dsimp only at multiplied
  rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 radiusPositive.ne'), one_smul] at multiplied
  have rotateIntegral := (rotation phase).measurePreserving.setIntegral_image_emb
    (rotation phase).toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun position => function (center + radius • position)) (nearCircleInterior data small)
  rw [imageIdentity, translation, multiplied.symm, rotateIntegral]
  rfl

end EulerNonuniqueness.Paper
