import EulerNonuniqueness.Section3.NearCircleInterior
import EulerNonuniqueness.Section3.AffineContourModel
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Data.Complex.FiniteDimensional

open Set MeasureTheory
open scoped Pointwise

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

def contourAffineHomeomorph (center : ℂ) {radius : ℝ} (positive : 0 < radius) : ℂ ≃ₜ ℂ :=
  (Homeomorph.smul (Units.mk0 radius positive.ne')).trans (Homeomorph.addLeft center)

theorem contourAffineHomeomorph_apply (center : ℂ) {radius : ℝ} (positive : 0 < radius) (position : ℂ) :
    contourAffineHomeomorph center positive position = center + radius • position := rfl

def affinePatchDomain (center : ℂ) (radius : ℝ) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) : Set ℂ :=
  (fun position => center + radius • position) '' nearCircleInterior data small

theorem affinePatchDomain_isOpen (center : ℂ) {radius : ℝ} (positive : 0 < radius)
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    IsOpen (affinePatchDomain center radius data small) :=
  (contourAffineHomeomorph center positive).isOpenMap _ (nearCircleInterior_isOpen data small)

theorem affinePatchDomain_isBounded (center : ℂ) {radius : ℝ} (positive : 0 < radius)
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    Bornology.IsBounded (affinePatchDomain center radius data small) := by
  have compact_image := (nearCircleInterior_isBounded data small).isCompact_closure.image
    (contourAffineHomeomorph center positive).continuous
  exact compact_image.isBounded.subset (image_mono subset_closure)

theorem affinePatchDomain_frontier (center : ℂ) {radius : ℝ} (positive : 0 < radius)
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    frontier (affinePatchDomain center radius data small) =
      Set.range (c1AffineContour center radius data).val.1 := by
  change frontier ((contourAffineHomeomorph center positive) '' nearCircleInterior data small) = _
  rw [← Homeomorph.image_frontier, nearCircleInterior_frontier data small, ← Set.range_comp]
  rfl

theorem integral_affinePatchDomain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (center : ℂ) {radius : ℝ} (positive : 0 < radius) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) (function : ℂ → E) :
    (∫ position in affinePatchDomain center radius data small, function position) =
      radius ^ 2 • (∫ position in nearCircleInterior data small, function (center + radius • position)) := by
  have image_identity : affinePatchDomain center radius data small =
      (fun position : ℂ => center + position) '' (radius • nearCircleInterior data small) := by
    rw [affinePatchDomain, ← Set.image_smul, Set.image_image]
  have translation := (measurePreserving_add_left (volume : Measure ℂ) center).setIntegral_image_emb
    (Homeomorph.addLeft center).toMeasurableEquiv.measurableEmbedding function
    (radius • nearCircleInterior data small)
  rw [image_identity, translation]
  have scaling := Measure.setIntegral_comp_smul_of_pos (volume : Measure ℂ)
    (fun position => function (center + position)) (nearCircleInterior data small) positive
  rw [Complex.finrank_real_complex] at scaling
  have multiplied := congrArg (fun value : E => radius ^ 2 • value) scaling
  dsimp only at multiplied
  rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 positive.ne'), one_smul] at multiplied
  exact multiplied.symm

theorem affinePatchDomain_area (center : ℂ) {radius : ℝ} (positive : 0 < radius)
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    (volume (affinePatchDomain center radius data small)).toReal =
      radius ^ 2 * (volume (nearCircleInterior data small)).toReal := by
  simpa only [setIntegral_const, smul_eq_mul, mul_one] using
    integral_affinePatchDomain center positive data small (fun _ => (1 : ℝ))

end

end EulerNonuniqueness.Paper
