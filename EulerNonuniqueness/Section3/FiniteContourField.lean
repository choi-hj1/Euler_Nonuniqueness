import EulerNonuniqueness.Section3.FiniteContourCrossLipschitz
import EulerNonuniqueness.Section3.BanachLocalEvolution

open Set Metric

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

local instance finiteContourFieldHolderNormedSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance finiteContourFieldC1NormedSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance finiteContourFieldBoundedSMul : IsBoundedSMul ℝ PeriodicC1HolderHalf :=
  NormedSpace.isBoundedSMul (𝕜 := ℝ) (E := PeriodicC1HolderHalf)

def standardContours (count : ℕ) : Fin count → PeriodicC1HolderHalf := fun _ => standardCircleBanach

def FiniteContourConfiguration.vectorField {count : ℕ} (configuration : FiniteContourConfiguration count)
    (data : Fin count → PeriodicC1HolderHalf) (index : Fin count) : PeriodicC1HolderHalf :=
  configuration.density index • extendedContourVelocity (data index) +
    ∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) •
      extendedCrossContourVelocity (configuration.physicalContour data index) (configuration.physicalContour data other)

def FiniteContourConfiguration.componentLipschitzConstant {count : ℕ}
    (configuration : FiniteContourConfiguration count) (radius : ℝ) (index : Fin count) : ℝ :=
  |configuration.density index| * contourVelocityBanachLipschitzConstant radius +
    ∑ other ∈ Finset.univ.erase index, |configuration.density other / configuration.radius index| *
      configuration.crossLipschitzCoefficient index other

def FiniteContourConfiguration.lipschitzConstant {count : ℕ}
    (configuration : FiniteContourConfiguration count) (radius : ℝ) : ℝ :=
  ∑ index, configuration.componentLipschitzConstant radius index

theorem FiniteContourConfiguration.componentLipschitzConstant_nonneg {count : ℕ}
    (configuration : FiniteContourConfiguration count) {radius : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi))) (index : Fin count) :
    0 ≤ configuration.componentLipschitzConstant radius index := by
  apply add_nonneg
  · exact mul_nonneg (abs_nonneg _) (contourVelocityBanachLipschitzConstant_nonneg radius_nonneg radius_small)
  · apply Finset.sum_nonneg
    intro other other_mem
    apply mul_nonneg (abs_nonneg _)
    exact configuration.crossLipschitzCoefficient_nonneg index other (Finset.ne_of_mem_erase other_mem).symm

theorem FiniteContourConfiguration.lipschitzConstant_nonneg {count : ℕ}
    (configuration : FiniteContourConfiguration count) {radius : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi))) :
    0 ≤ configuration.lipschitzConstant radius :=
  Finset.sum_nonneg (fun index _ => configuration.componentLipschitzConstant_nonneg radius_nonneg radius_small index)

theorem near_standardContours_component {count : ℕ} (data : Fin count → PeriodicC1HolderHalf)
    {radius : ℝ} (nearby : ‖data - standardContours count‖ ≤ radius) (index : Fin count) :
    ‖data index - standardCircleBanach‖ ≤ radius :=
  (norm_le_pi_norm (data - standardContours count) index).trans nearby

theorem near_standardContours_norm_bound {count : ℕ} (data : Fin count → PeriodicC1HolderHalf)
    {radius : ℝ} (nearby : ‖data - standardContours count‖ ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi))) (index : Fin count) : ‖data index‖ ≤ 3 := by
  have bound := PeriodicC1HolderHalf.norm_le_radius_add_two (data index)
    (near_standardContours_component data nearby index)
  have radius_lt_one := radius_small.trans_le (min_le_left _ _)
  linarith

set_option maxHeartbeats 1000000 in
theorem FiniteContourConfiguration.vectorField_component_parameter_norm_bound {count : ℕ}
    (configuration : FiniteContourConfiguration count) (first second : Fin count → PeriodicC1HolderHalf)
    {radius : ℝ} (radius_nonneg : 0 ≤ radius) (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardContours count‖ ≤ radius)
    (second_near : ‖second - standardContours count‖ ≤ radius) (index : Fin count) :
    ‖configuration.vectorField first index - configuration.vectorField second index‖ ≤
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
  have cross_bound : ∀ other ∈ Finset.univ.erase index,
      ‖extendedCrossContourVelocity (configuration.physicalContour first index) (configuration.physicalContour first other) -
        extendedCrossContourVelocity (configuration.physicalContour second index) (configuration.physicalContour second other)‖ ≤
      configuration.crossLipschitzCoefficient index other * ‖first - second‖ := by
    intro other other_mem
    exact configuration.cross_velocity_parameter_norm_bound first second index other
      (Finset.ne_of_mem_erase other_mem).symm
      (near_standardContours_norm_bound first first_near radius_small)
      (near_standardContours_norm_bound second second_near radius_small)
  have identity : configuration.vectorField first index - configuration.vectorField second index =
      configuration.density index • (extendedContourVelocity (first index) - extendedContourVelocity (second index)) +
      ∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) •
        (extendedCrossContourVelocity (configuration.physicalContour first index) (configuration.physicalContour first other) -
          extendedCrossContourVelocity (configuration.physicalContour second index) (configuration.physicalContour second other)) := by
    have cross_identity :
        (∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) •
          (extendedCrossContourVelocity (configuration.physicalContour first index) (configuration.physicalContour first other) -
            extendedCrossContourVelocity (configuration.physicalContour second index) (configuration.physicalContour second other))) =
        (∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) •
          extendedCrossContourVelocity (configuration.physicalContour first index) (configuration.physicalContour first other)) -
        ∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) •
          extendedCrossContourVelocity (configuration.physicalContour second index) (configuration.physicalContour second other) := by
      rw [← Finset.sum_sub_distrib (s := Finset.univ.erase index)
        (f := fun other => (configuration.density other / configuration.radius index) •
          extendedCrossContourVelocity (configuration.physicalContour first index) (configuration.physicalContour first other))
        (g := fun other => (configuration.density other / configuration.radius index) •
          extendedCrossContourVelocity (configuration.physicalContour second index) (configuration.physicalContour second other))]
      apply Finset.sum_congr rfl
      intro other other_mem
      exact smul_sub (configuration.density other / configuration.radius index)
        (extendedCrossContourVelocity (configuration.physicalContour first index) (configuration.physicalContour first other))
        (extendedCrossContourVelocity (configuration.physicalContour second index) (configuration.physicalContour second other))
    rw [cross_identity, smul_sub (configuration.density index)
      (extendedContourVelocity (first index)) (extendedContourVelocity (second index))]
    unfold FiniteContourConfiguration.vectorField
    abel
  rw [identity]
  apply (norm_add_le
    (configuration.density index • (extendedContourVelocity (first index) - extendedContourVelocity (second index)))
    (∑ other ∈ Finset.univ.erase index, (configuration.density other / configuration.radius index) •
      (extendedCrossContourVelocity (configuration.physicalContour first index) (configuration.physicalContour first other) -
        extendedCrossContourVelocity (configuration.physicalContour second index) (configuration.physicalContour second other)))).trans
  apply (add_le_add (le_refl _) (norm_sum_le
    (Finset.univ.erase index)
    (fun other => (configuration.density other / configuration.radius index) •
      (extendedCrossContourVelocity (configuration.physicalContour first index) (configuration.physicalContour first other) -
        extendedCrossContourVelocity (configuration.physicalContour second index) (configuration.physicalContour second other))))).trans
  rw [norm_smul (configuration.density index)
    (extendedContourVelocity (first index) - extendedContourVelocity (second index)), Real.norm_eq_abs]
  have self_scaled := mul_le_mul_of_nonneg_left self_bound (abs_nonneg (configuration.density index))
  have sum_scaled :
      (∑ other ∈ Finset.univ.erase index, ‖(configuration.density other / configuration.radius index) •
        (extendedCrossContourVelocity (configuration.physicalContour first index) (configuration.physicalContour first other) -
          extendedCrossContourVelocity (configuration.physicalContour second index) (configuration.physicalContour second other))‖) ≤
      ∑ other ∈ Finset.univ.erase index, |configuration.density other / configuration.radius index| *
        (configuration.crossLipschitzCoefficient index other * ‖first - second‖) := by
    apply Finset.sum_le_sum
    intro other other_mem
    rw [norm_smul (configuration.density other / configuration.radius index)
      (extendedCrossContourVelocity (configuration.physicalContour first index) (configuration.physicalContour first other) -
        extendedCrossContourVelocity (configuration.physicalContour second index) (configuration.physicalContour second other)), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (cross_bound other other_mem) (abs_nonneg _)
  apply (add_le_add self_scaled sum_scaled).trans_eq
  unfold FiniteContourConfiguration.componentLipschitzConstant
  rw [add_mul, Finset.sum_mul]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro other other_mem
    ring

set_option maxHeartbeats 1000000 in
theorem FiniteContourConfiguration.vectorField_parameter_norm_bound {count : ℕ}
    (configuration : FiniteContourConfiguration count) (first second : Fin count → PeriodicC1HolderHalf)
    {radius : ℝ} (radius_nonneg : 0 ≤ radius) (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardContours count‖ ≤ radius)
    (second_near : ‖second - standardContours count‖ ≤ radius) :
    ‖configuration.vectorField first - configuration.vectorField second‖ ≤
      configuration.lipschitzConstant radius * ‖first - second‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg
    (configuration.lipschitzConstant_nonneg radius_nonneg radius_small) (norm_nonneg _))).mpr
  intro index
  have component := configuration.vectorField_component_parameter_norm_bound first second radius_nonneg radius_small
    first_near second_near index
  have constant_le : configuration.componentLipschitzConstant radius index ≤ configuration.lipschitzConstant radius :=
    Finset.single_le_sum (fun other _ => configuration.componentLipschitzConstant_nonneg radius_nonneg radius_small other)
      (Finset.mem_univ index)
  exact component.trans (mul_le_mul_of_nonneg_right constant_le (norm_nonneg _))

set_option maxHeartbeats 1000000 in
theorem FiniteContourConfiguration.vectorField_lipschitzOn_ball {count : ℕ}
    (configuration : FiniteContourConfiguration count) {radius : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi))) :
    LipschitzOnWith ⟨configuration.lipschitzConstant radius,
      configuration.lipschitzConstant_nonneg radius_nonneg radius_small⟩ configuration.vectorField
      (closedBall (standardContours count) radius) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro first first_mem second second_mem
  have first_near : ‖first - standardContours count‖ ≤ radius :=
    (dist_eq_norm first (standardContours count)) ▸ first_mem
  have second_near : ‖second - standardContours count‖ ≤ radius :=
    (dist_eq_norm second (standardContours count)) ▸ second_mem
  rw [dist_eq_norm (configuration.vectorField first) (configuration.vectorField second), dist_eq_norm first second]
  exact configuration.vectorField_parameter_norm_bound first second radius_nonneg radius_small first_near second_near

end

end EulerNonuniqueness.Paper
