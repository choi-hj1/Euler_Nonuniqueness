import EulerNonuniqueness.Section3.AffinePatchDomain
import EulerNonuniqueness.Section3.NearCircleExteriorBiotSavart

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

theorem biotSavartKernel_real_scaling {radius : ℝ} (positive : 0 < radius) (position : ℂ) :
    biotSavartKernel (radius • position) = radius⁻¹ • biotSavartKernel position := by
  by_cases zero : position = 0
  · simp [zero, biotSavartKernel]
  have radius_nonzero : (radius : ℂ) ≠ 0 := by exact_mod_cast positive.ne'
  have denominator_nonzero : ((2 * Real.pi * ‖position‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : 2 * Real.pi * ‖position‖ ^ 2 ≠ 0)
  have norm_nonzero : (‖position‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr zero)
  have pi_nonzero : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [biotSavartKernel, norm_smul radius position, Real.norm_eq_abs, abs_of_pos positive, biotSavartKernel]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_pow]
  field_simp [radius_nonzero, norm_nonzero, pi_nonzero]
  <;> ring

theorem integral_affinePatchDomain_biotSavart_scaling
    (center : ℂ) {radius : ℝ} (positive : 0 < radius) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) (point : ℂ) :
    (∫ position in affinePatchDomain center radius data small,
      biotSavartKernel ((center + radius • point) - position)) =
      radius • (∫ position in nearCircleInterior data small, biotSavartKernel (point - position)) := by
  rw [integral_affinePatchDomain center positive data small]
  have difference (position : ℂ) : center + radius • point - (center + radius • position) =
      radius • (point - position) := by rw [smul_sub]; abel
  simp_rw [difference, biotSavartKernel_real_scaling positive]
  rw [integral_smul, smul_smul]
  congr 1
  field_simp
  <;> ring

theorem integral_affinePatchDomain_biotSavart_boundary
    (center : ℂ) {radius : ℝ} (positive : 0 < radius) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (chord_small : ‖data - standardCircleBanach‖ < 2 / (3 * Real.pi)) (target : ℝ) :
    (∫ position in affinePatchDomain center radius data small,
      biotSavartKernel ((c1AffineContour center radius data).val.1 target - position)) =
      pointContourVelocity (c1AffineContour center radius data).val.1
        (c1AffineContour center radius data).val.2.val.1
        ((c1AffineContour center radius data).val.1 target) (-Real.pi) Real.pi := by
  rw [c1AffineContour_value, integral_affinePatchDomain_biotSavart_scaling center positive data small,
    integral_nearCircleInterior_biotSavart_boundary data small chord_small]
  exact (c1AffineContour_self_velocity center positive data
    (lt_min (small.trans (by norm_num)) chord_small) target).symm

theorem integral_affinePatchDomain_biotSavart_off_boundary
    (center : ℂ) {radius : ℝ} (positive : 0 < radius) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (chord_small : ‖data - standardCircleBanach‖ < 2 / (3 * Real.pi)) (point : ℂ)
    (off_boundary : point ∉ frontier (affinePatchDomain center radius data small)) :
    (∫ position in affinePatchDomain center radius data small, biotSavartKernel (point - position)) =
      pointContourVelocity (c1AffineContour center radius data).val.1
        (c1AffineContour center radius data).val.2.val.1 point (-Real.pi) Real.pi := by
  let normalized : ℂ := radius⁻¹ • (point - center)
  have point_identity : center + radius • normalized = point := by
    dsimp only [normalized]
    rw [smul_smul, mul_inv_cancel₀ positive.ne', one_smul]
    abel
  have separated (label : ℝ) : data.val.1 label ≠ normalized := by
    intro equality
    apply off_boundary
    rw [affinePatchDomain_frontier center positive data small]
    refine ⟨label, ?_⟩
    rw [c1AffineContour_value, equality, point_identity]
  have log_continuous : Continuous (fun label => Real.log ‖data.val.1 label - normalized‖) :=
    (data.val.1.continuous.sub continuous_const).norm.log
      (fun label => norm_ne_zero_iff.mpr (sub_ne_zero.mpr (separated label)))
  have tangent_integrable : IntervalIntegrable data.val.2.val.1 volume (-Real.pi) Real.pi :=
    data.val.2.val.1.continuous.intervalIntegrable _ _
  have log_integrable : IntervalIntegrable
      (fun label => Real.log ‖data.val.1 label - normalized‖ • data.val.2.val.1 label)
      volume (-Real.pi) Real.pi :=
    (log_continuous.smul data.val.2.val.1.continuous).intervalIntegrable _ _
  have separated_ae : ∀ᵐ source ∂volume, source ∈ uIoc (-Real.pi) Real.pi → data.val.1 source - normalized ≠ 0 :=
    Filter.Eventually.of_forall fun label _ => sub_ne_zero.mpr (separated label)
  have tangent_zero : (∫ label in (-Real.pi)..Real.pi, data.val.2.val.1 label) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun label _ => PeriodicC1HolderHalf.hasDerivAt data label) tangent_integrable]
    have periodic := PeriodicC1HolderHalf.periodic data (-Real.pi)
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at periodic
    rw [periodic, sub_self]
  have covariance := pointContourVelocity_scaling data.val.1 data.val.2.val.1 normalized center
    positive tangent_integrable log_integrable separated_ae tangent_zero
  have tangent_identity : (fun source => radius • data.val.2.val.1 source) =
      (c1AffineContour center radius data).val.2.val.1 := by
    funext source
    exact (c1AffineContour_tangent center radius data source).symm
  rw [tangent_identity] at covariance
  change pointContourVelocity (c1AffineContour center radius data).val.1
    (c1AffineContour center radius data).val.2.val.1 (center + radius • normalized) (-Real.pi) Real.pi =
      radius • pointContourVelocity data.val.1 data.val.2.val.1 normalized (-Real.pi) Real.pi at covariance
  rw [point_identity] at covariance
  have velocity := integral_affinePatchDomain_biotSavart_scaling center positive data small normalized
  rw [point_identity, integral_nearCircleInterior_biotSavart_all_points data small chord_small] at velocity
  exact velocity.trans covariance.symm

theorem integral_affinePatchDomain_biotSavart_all_points
    (center : ℂ) {radius : ℝ} (positive : 0 < radius) (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (chord_small : ‖data - standardCircleBanach‖ < 2 / (3 * Real.pi)) (point : ℂ) :
    (∫ position in affinePatchDomain center radius data small, biotSavartKernel (point - position)) =
      pointContourVelocity (c1AffineContour center radius data).val.1
        (c1AffineContour center radius data).val.2.val.1 point (-Real.pi) Real.pi := by
  by_cases on_boundary : point ∈ frontier (affinePatchDomain center radius data small)
  · rw [affinePatchDomain_frontier center positive data small] at on_boundary
    obtain ⟨target, rfl⟩ := on_boundary
    exact integral_affinePatchDomain_biotSavart_boundary center positive data small chord_small target
  · exact integral_affinePatchDomain_biotSavart_off_boundary center positive data small chord_small point on_boundary

end

end EulerNonuniqueness.Paper
