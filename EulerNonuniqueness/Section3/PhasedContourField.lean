import EulerNonuniqueness.Section3.PhasedContourGeometry

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance phasedContourFieldRealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem unitRotationC1_norm (phase : Circle) (data : PeriodicC1HolderHalf) :
    ‖(phase : ℂ) • data‖ = ‖data‖ := by
  change ‖(phase : ℂ) • data.val‖ = ‖data.val‖
  rw [norm_smul (phase : ℂ) data.val, Circle.norm_coe, one_mul]

theorem unitRotationC1_sub (phase : Circle) (first second : PeriodicC1HolderHalf) :
    (phase : ℂ) • first - (phase : ℂ) • second = (phase : ℂ) • (first - second) := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (phase : ℂ) * first.val.1 label - (phase : ℂ) * second.val.1 label =
    (phase : ℂ) * (first.val.1 label - second.val.1 label)
  exact (mul_sub _ _ _).symm

def FiniteContourConfiguration.phasedVectorField {count : ℕ}
    (configuration : FiniteContourConfiguration count) (phase : Fin count → Circle)
    (data : Fin count → PeriodicC1HolderHalf) (index : Fin count) : PeriodicC1HolderHalf :=
  configuration.density index • extendedContourVelocity (data index) +
    ∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) •
      (((phase index)⁻¹ : Circle) : ℂ) • extendedCrossContourVelocity
        (configuration.phasedPhysicalContour phase data index) (configuration.phasedPhysicalContour phase data other)

theorem FiniteContourConfiguration.phasedVectorField_component_parameter_norm_bound {count : ℕ}
    (configuration : FiniteContourConfiguration count) (phase : Fin count → Circle)
    (first second : Fin count → PeriodicC1HolderHalf)
    {radius : ℝ} (radius_nonneg : 0 ≤ radius) (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardContours count‖ ≤ radius)
    (second_near : ‖second - standardContours count‖ ≤ radius) (index : Fin count) :
    ‖configuration.phasedVectorField phase first index - configuration.phasedVectorField phase second index‖ ≤
      configuration.componentLipschitzConstant radius index * ‖first - second‖ := by
  have self_bound : ‖extendedContourVelocity (first index) - extendedContourVelocity (second index)‖ ≤
      contourVelocityBanachLipschitzConstant radius * ‖first - second‖ := by
    have first_component := near_standardContours_component first first_near index
    have second_component := near_standardContours_component second second_near index
    rw [extendedContourVelocity_eq (first index) (first_component.trans_lt radius_small),
      extendedContourVelocity_eq (second index) (second_component.trans_lt radius_small)]
    exact (contourVelocityBanach_parameter_norm_bound _ _ radius_nonneg radius_small first_component second_component).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm (first - second) index)
        (contourVelocityBanachLipschitzConstant_nonneg radius_nonneg radius_small))
  let firstCross := fun other => extendedCrossContourVelocity
    (configuration.phasedPhysicalContour phase first index) (configuration.phasedPhysicalContour phase first other)
  let secondCross := fun other => extendedCrossContourVelocity
    (configuration.phasedPhysicalContour phase second index) (configuration.phasedPhysicalContour phase second other)
  have cross_bound : ∀ other ∈ Finset.univ.erase index,
      ‖firstCross other - secondCross other‖ ≤
        configuration.crossLipschitzCoefficient index other * ‖first - second‖ := by
    intro other member
    exact configuration.phased_cross_velocity_parameter_norm_bound phase first second index other
      (Finset.ne_of_mem_erase member).symm
      (near_standardContours_norm_bound first first_near radius_small)
      (near_standardContours_norm_bound second second_near radius_small)
  have difference : configuration.phasedVectorField phase first index - configuration.phasedVectorField phase second index =
      configuration.density index • (extendedContourVelocity (first index) - extendedContourVelocity (second index)) +
      ∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) •
        (((phase index)⁻¹ : Circle) : ℂ) • (firstCross other - secondCross other) := by
    have sum_difference :
        (∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) •
          (((phase index)⁻¹ : Circle) : ℂ) • (firstCross other - secondCross other)) =
        (∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) •
          (((phase index)⁻¹ : Circle) : ℂ) • firstCross other) -
        ∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) •
          (((phase index)⁻¹ : Circle) : ℂ) • secondCross other := by
      rw [← Finset.sum_sub_distrib (s := Finset.univ.erase index)
        (f := fun other => (configuration.density other / configuration.radius index) •
          (((phase index)⁻¹ : Circle) : ℂ) • firstCross other)
        (g := fun other => (configuration.density other / configuration.radius index) •
          (((phase index)⁻¹ : Circle) : ℂ) • secondCross other)]
      apply Finset.sum_congr rfl
      intro other member
      rw [← unitRotationC1_sub]
      exact smul_sub (configuration.density other / configuration.radius index)
        ((((phase index)⁻¹ : Circle) : ℂ) • firstCross other)
        ((((phase index)⁻¹ : Circle) : ℂ) • secondCross other)
    rw [sum_difference, smul_sub (configuration.density index)
      (extendedContourVelocity (first index)) (extendedContourVelocity (second index))]
    dsimp only [FiniteContourConfiguration.phasedVectorField, firstCross, secondCross]
    abel
  rw [difference]
  apply (norm_add_le
    (configuration.density index • (extendedContourVelocity (first index) - extendedContourVelocity (second index)))
    (∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) •
      (((phase index)⁻¹ : Circle) : ℂ) • (firstCross other - secondCross other))).trans
  apply (add_le_add (le_refl _) (norm_sum_le (Finset.univ.erase index)
    (fun other => (configuration.density other / configuration.radius index) •
      (((phase index)⁻¹ : Circle) : ℂ) • (firstCross other - secondCross other)))).trans
  rw [norm_smul (configuration.density index)
    (extendedContourVelocity (first index) - extendedContourVelocity (second index)), Real.norm_eq_abs]
  have self_scaled := mul_le_mul_of_nonneg_left self_bound (abs_nonneg (configuration.density index))
  have sum_scaled :
      (∑ other ∈ Finset.univ.erase index, ‖(configuration.density other / configuration.radius index) •
        (((phase index)⁻¹ : Circle) : ℂ) • (firstCross other - secondCross other)‖) ≤
      ∑ other ∈ Finset.univ.erase index, |configuration.density other / configuration.radius index| *
        (configuration.crossLipschitzCoefficient index other * ‖first - second‖) := by
    apply Finset.sum_le_sum
    intro other member
    rw [norm_smul (configuration.density other / configuration.radius index)
      ((((phase index)⁻¹ : Circle) : ℂ) • (firstCross other - secondCross other)), Real.norm_eq_abs,
      unitRotationC1_norm]
    exact mul_le_mul_of_nonneg_left (cross_bound other member) (abs_nonneg _)
  apply (add_le_add self_scaled sum_scaled).trans_eq
  unfold FiniteContourConfiguration.componentLipschitzConstant
  rw [add_mul, Finset.sum_mul]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro other member
    ring

theorem FiniteContourConfiguration.phasedVectorField_parameter_norm_bound {count : ℕ}
    (configuration : FiniteContourConfiguration count) (phase : Fin count → Circle)
    (first second : Fin count → PeriodicC1HolderHalf)
    {radius : ℝ} (radius_nonneg : 0 ≤ radius) (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardContours count‖ ≤ radius)
    (second_near : ‖second - standardContours count‖ ≤ radius) :
    ‖configuration.phasedVectorField phase first - configuration.phasedVectorField phase second‖ ≤
      configuration.lipschitzConstant radius * ‖first - second‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg
    (configuration.lipschitzConstant_nonneg radius_nonneg radius_small) (norm_nonneg _))).mpr
  intro index
  have component := configuration.phasedVectorField_component_parameter_norm_bound phase first second
    radius_nonneg radius_small first_near second_near index
  have constant_le : configuration.componentLipschitzConstant radius index ≤ configuration.lipschitzConstant radius :=
    Finset.single_le_sum (fun other _ => configuration.componentLipschitzConstant_nonneg radius_nonneg radius_small other)
      (Finset.mem_univ index)
  exact component.trans (mul_le_mul_of_nonneg_right constant_le (norm_nonneg _))

theorem FiniteContourConfiguration.phasedVectorField_lipschitzOn_ball {count : ℕ}
    (configuration : FiniteContourConfiguration count) (phase : Fin count → Circle)
    {radius : ℝ} (radius_nonneg : 0 ≤ radius) (radius_small : radius < min 1 (2 / (3 * Real.pi))) :
    LipschitzOnWith ⟨configuration.lipschitzConstant radius,
      configuration.lipschitzConstant_nonneg radius_nonneg radius_small⟩ (configuration.phasedVectorField phase)
      (closedBall (standardContours count) radius) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro first first_mem second second_mem
  rw [dist_eq_norm (configuration.phasedVectorField phase first) (configuration.phasedVectorField phase second),
    dist_eq_norm first second]
  apply configuration.phasedVectorField_parameter_norm_bound phase first second radius_nonneg radius_small
  · exact (dist_eq_norm first (standardContours count)) ▸ first_mem
  · exact (dist_eq_norm second (standardContours count)) ▸ second_mem

end EulerNonuniqueness.Paper
