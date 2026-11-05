import EulerNonuniqueness.Section3.MovingMaterialPatch
import EulerNonuniqueness.Section3.NearCircleFamilyAngles
import EulerNonuniqueness.General.PolarFamilyOpen

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace EulerNonuniqueness.Paper.MovingMaterialPatch

def normalizedPosition (path : MovingMaterialPatch) (point : ℝ × ℂ) : ℂ :=
  (Circle.exp (path.phase point.1) : ℂ)⁻¹ * (path.radius⁻¹ • (point.2 - path.center point.1))

theorem continuous_normalizedPosition (path : MovingMaterialPatch) : Continuous path.normalizedPosition := by
  have rotationContinuous : Continuous (fun point : ℝ × ℂ => ((Circle.exp (path.phase point.1))⁻¹ : Circle)) :=
    ((Circle.exp.continuous.comp path.phase_continuous).comp continuous_fst).inv
  exact (continuous_subtype_val.comp rotationContinuous).mul
    (continuous_const.smul (continuous_snd.sub (path.center_continuous.comp continuous_fst)))

theorem normalizedPosition_physical (path : MovingMaterialPatch) (time : ℝ) (position : ℂ) :
    path.center time + path.radius • ((Circle.exp (path.phase time) : ℂ) *
      path.normalizedPosition (time, position)) = position := by
  simp only [normalizedPosition, mul_inv_cancel_left₀ (Circle.coe_ne_zero _), smul_smul,
    mul_inv_cancel₀ path.radius_positive.ne', one_smul, add_sub_cancel]

theorem normalizedPosition_boundary_image (path : MovingMaterialPatch) (time : ℝ) (position : ℂ) :
    path.normalizedPosition (time, path.center time + path.radius •
      ((Circle.exp (path.phase time) : ℂ) * position)) = position := by
  simp only [normalizedPosition, add_sub_cancel_left, smul_smul,
    inv_mul_cancel₀ path.radius_positive.ne', one_smul, inv_mul_cancel_left₀ (Circle.coe_ne_zero _)]

theorem domain_mem_iff (path : MovingMaterialPatch) (point : ℝ × ℂ) :
    point.2 ∈ path.domain point.1 ↔
      path.normalizedPosition point ∈ nearCircleInterior (path.shape point.1) (path.nearby point.1) := by
  constructor
  · rintro ⟨position, member, identity⟩
    change path.normalizedPosition (point.1, point.2) ∈ nearCircleInterior (path.shape point.1) (path.nearby point.1)
    rw [← identity, path.normalizedPosition_boundary_image]
    exact member
  · intro member
    exact ⟨_, member, path.normalizedPosition_physical point.1 point.2⟩

theorem spacetime_domain_isOpen (path : MovingMaterialPatch) :
    IsOpen {point : ℝ × ℂ | point.2 ∈ path.domain point.1} := by
  have openNormalized := isOpen_periodic_polar_family
    (fun time angle => nearCircleRadialProfile (path.shape time) (path.nearby time) angle)
    (continuous_nearCircleRadialProfile_joint path.shape path.shape_continuous path.nearby)
    (fun time => nearCircleRadialProfile_periodic (path.shape time) (path.nearby time))
    (by norm_num : 0 < (2 / 3 : ℝ))
    (fun time angle => by linarith [nearCircleRadialProfile_lower (path.shape time) (path.nearby time) angle, path.nearby time])
  convert openNormalized.preimage (continuous_fst.prodMk path.continuous_normalizedPosition) using 1
  ext point
  exact path.domain_mem_iff point

theorem measurable_domain_indicator (path : MovingMaterialPatch) :
    Measurable (fun point : ℝ × ℂ => (path.domain point.1).indicator (fun _ => (1 : ℝ)) point.2) := by
  have result : Measurable
      ({point : ℝ × ℂ | point.2 ∈ path.domain point.1}.indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator path.spacetime_domain_isOpen.measurableSet
  convert result using 1

theorem domain_persistence (path : MovingMaterialPatch) (time : ℝ)
    (position : ℂ) (member : position ∈ path.domain time) :
    ∀ᶠ parameter in 𝓝 time, position ∈ path.domain parameter := by
  exact (path.spacetime_domain_isOpen.preimage (continuous_id.prodMk continuous_const)).mem_nhds member

end EulerNonuniqueness.Paper.MovingMaterialPatch
