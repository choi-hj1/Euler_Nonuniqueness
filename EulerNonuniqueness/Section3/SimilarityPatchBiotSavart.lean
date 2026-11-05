import EulerNonuniqueness.Section3.SimilarityPatchDomain
import EulerNonuniqueness.Section3.AffinePatchBiotSavart
import EulerNonuniqueness.Section3.ContourRotation

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem integral_similarityPatchDomain_biotSavart_scaling
    (center : ℂ) {radius : ℝ} (positive : 0 < radius) (phase : Circle)
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3) (point : ℂ) :
    (∫ position in similarityPatchDomain center radius phase data small,
      biotSavartKernel ((center + radius • ((phase : ℂ) * point)) - position)) =
      radius • ((phase : ℂ) * (∫ position in nearCircleInterior data small, biotSavartKernel (point - position))) := by
  rw [integral_similarityPatchDomain center positive phase data small]
  have difference (position : ℂ) :
      center + radius • ((phase : ℂ) * point) - (center + radius • ((phase : ℂ) * position)) =
      radius • ((phase : ℂ) * (point - position)) := by
    simp only [Complex.real_smul]
    ring
  simp_rw [difference, biotSavartKernel_real_scaling positive,
    biotSavartKernel_unit_rotation _ _ (Circle.norm_coe phase)]
  rw [integral_smul, integral_const_mul, smul_smul]
  congr 1
  field_simp
  <;> ring

theorem integral_similarityPatchDomain_biotSavart_at_normalized_point
    (center : ℂ) {radius : ℝ} (positive : 0 < radius) (phase : Circle)
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (chord_small : ‖data - standardCircleBanach‖ < 2 / (3 * Real.pi)) (point : ℂ) :
    (∫ position in similarityPatchDomain center radius phase data small,
      biotSavartKernel ((center + radius • ((phase : ℂ) * point)) - position)) =
      pointContourVelocity (fun label => center + radius • ((phase : ℂ) * data.val.1 label))
        (fun label => radius • ((phase : ℂ) * data.val.2.val.1 label))
        (center + radius • ((phase : ℂ) * point)) (-Real.pi) Real.pi := by
  have affine := integral_affinePatchDomain_biotSavart_scaling 0 positive data small point
  rw [integral_affinePatchDomain_biotSavart_all_points 0 positive data small chord_small] at affine
  have rotated := pointContourVelocity_unit_rotation
    (c1AffineContour 0 radius data).val.1 (c1AffineContour 0 radius data).val.2.val.1
    (0 + radius • point) (phase : ℂ) center (Circle.norm_coe phase) (-Real.pi) Real.pi
  have curveIdentity : (fun label => (phase : ℂ) * (c1AffineContour 0 radius data).val.1 label + center) =
      (fun label => center + radius • ((phase : ℂ) * data.val.1 label)) := by
    funext label
    rw [c1AffineContour_value]
    simp only [zero_add, Complex.real_smul]
    ring
  have tangentIdentity : (fun label => (phase : ℂ) * (c1AffineContour 0 radius data).val.2.val.1 label) =
      (fun label => radius • ((phase : ℂ) * data.val.2.val.1 label)) := by
    funext label
    rw [c1AffineContour_tangent]
    simp only [Complex.real_smul]
    ring
  have pointIdentity : (phase : ℂ) * (0 + radius • point) + center =
      center + radius • ((phase : ℂ) * point) := by
    simp only [zero_add, Complex.real_smul]
    ring
  rw [curveIdentity, tangentIdentity, pointIdentity, affine] at rotated
  rw [integral_similarityPatchDomain_biotSavart_scaling center positive phase data small]
  exact (by simpa only [Complex.real_smul, mul_left_comm] using rotated.symm)

theorem integral_similarityPatchDomain_biotSavart_all_points
    (center : ℂ) {radius : ℝ} (positive : 0 < radius) (phase : Circle)
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (chord_small : ‖data - standardCircleBanach‖ < 2 / (3 * Real.pi)) (point : ℂ) :
    (∫ position in similarityPatchDomain center radius phase data small, biotSavartKernel (point - position)) =
      pointContourVelocity (fun label => center + radius • ((phase : ℂ) * data.val.1 label))
        (fun label => radius • ((phase : ℂ) * data.val.2.val.1 label)) point (-Real.pi) Real.pi := by
  obtain ⟨normalized, equality⟩ := (contourSimilarityHomeomorph center positive phase).surjective point
  change center + radius • ((phase : ℂ) * normalized) = point at equality
  rw [← equality]
  exact integral_similarityPatchDomain_biotSavart_at_normalized_point center positive phase data small chord_small normalized

theorem similarityContour_self_velocity
    (center : ℂ) {radius : ℝ} (positive : 0 < radius) (phase : Circle)
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (chord_small : ‖data - standardCircleBanach‖ < 2 / (3 * Real.pi)) (label : ℝ) :
    pointContourVelocity (fun source => center + radius • ((phase : ℂ) * data.val.1 source))
        (fun source => radius • ((phase : ℂ) * data.val.2.val.1 source))
        (center + radius • ((phase : ℂ) * data.val.1 label)) (-Real.pi) Real.pi =
      radius • ((phase : ℂ) * contourVelocity data.val.1 data.val.2.val.1 label (-Real.pi) Real.pi) := by
  rw [← integral_similarityPatchDomain_biotSavart_all_points center positive phase data small chord_small,
    integral_similarityPatchDomain_biotSavart_scaling center positive phase data small,
    integral_nearCircleInterior_biotSavart_boundary data small chord_small]

end EulerNonuniqueness.Paper
