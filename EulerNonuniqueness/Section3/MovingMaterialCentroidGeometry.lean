import EulerNonuniqueness.Section3.MovingMaterialPatchMoments
import EulerNonuniqueness.Section3.ContourAnalyticCentroid

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.MovingMaterialPatch

theorem centroid_eq_center_add_contourCentroid (path : MovingMaterialPatch) (time : ℝ) :
    path.centroid time = path.center time + path.radius •
      ((Circle.exp (path.phase time) : ℂ) * contourCentroidFunctional (path.shape time)) := by
  let domain := nearCircleInterior (path.shape time) (path.nearby time)
  have domainFinite : volume domain < ⊤ :=
    (nearCircleInterior_isBounded (path.shape time) (path.nearby time)).measure_lt_top
  have domainPositive : 0 < volume.real domain := by
    change 0 < (volume (nearCircleInterior (path.shape time) (path.nearby time))).toReal
    rw [← contourAreaFunctional_eq_domain_area (path.shape time) (path.nearby time)]
    exact contourAreaFunctional_pos (path.shape time) (path.nearby time)
  have positionIntegrable : IntegrableOn (fun position : ℂ => position) domain :=
    (continuous_id.continuousOn.integrableOn_compact
      (nearCircleInterior_isBounded (path.shape time) (path.nearby time)).isCompact_closure).mono_set subset_closure
  have constantIntegrable : IntegrableOn (fun _ : ℂ => path.center time) domain :=
    integrableOn_const.mpr (Or.inr domainFinite)
  have areaIdentity : volume.real (path.domain time) = path.radius ^ 2 * volume.real domain := by
    have identity := integral_similarityPatchDomain (path.center time) path.radius_positive
      (Circle.exp (path.phase time)) (path.shape time) (path.nearby time) (fun _ => (1 : ℝ))
    simpa only [domain, MovingMaterialPatch.domain, setIntegral_const, Measure.real,
      Measure.restrict_apply_univ, smul_eq_mul, mul_one] using identity
  have momentIdentity : (∫ position in path.domain time, position) = path.radius ^ 2 •
      (volume.real domain • path.center time + path.radius •
        ((Circle.exp (path.phase time) : ℂ) * ∫ position in domain, position)) := by
    rw [MovingMaterialPatch.domain, integral_similarityPatchDomain (path.center time) path.radius_positive]
    congr 1
    change (∫ position in domain, path.center time + path.radius •
      ((Circle.exp (path.phase time) : ℂ) * position)) = _
    have scaledIntegrable : IntegrableOn (fun position : ℂ => path.radius •
        ((Circle.exp (path.phase time) : ℂ) * position)) domain :=
      (positionIntegrable.const_mul _).smul _
    rw [integral_add constantIntegrable scaledIntegrable, integral_smul,
      integral_const_mul, setIntegral_const]
  rw [centroid, areaIdentity, momentIdentity,
    contourCentroidFunctional_eq_domain_centroid (path.shape time) (path.nearby time)]
  change (path.radius ^ 2 * volume.real domain)⁻¹ • (path.radius ^ 2 •
    (volume.real domain • path.center time + path.radius •
      ((Circle.exp (path.phase time) : ℂ) * ∫ position in domain, position))) = _
  simp only [Complex.real_smul, map_inv₀, map_mul, map_pow]
  have radiusNonzero : (path.radius : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr path.radius_positive.ne'
  have areaNonzero : (volume.real domain : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr domainPositive.ne'
  change _ = path.center time + (path.radius : ℂ) *
    ((Circle.exp (path.phase time) : ℂ) * ((∫ position in domain, position) / (volume.real domain : ℂ)))
  field_simp
  ring

theorem centroid_eq_center_of_contourCentroid_zero (path : MovingMaterialPatch) (time : ℝ)
    (centered : contourCentroidFunctional (path.shape time) = 0) :
    path.centroid time = path.center time := by
  rw [path.centroid_eq_center_add_contourCentroid time, centered, mul_zero, smul_zero, add_zero]

end EulerNonuniqueness.Paper.MovingMaterialPatch
