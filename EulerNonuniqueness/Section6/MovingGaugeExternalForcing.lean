import EulerNonuniqueness.Section6.FiniteDomainSpatialContourField
import EulerNonuniqueness.Section3.MovingCentroidGaugeShapeEquation

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance gaugeExternalC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph
local instance gaugeExternalDerivativeGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := ℂ) (σ₁₂ := RingHom.id ℝ)

variable {count : ℕ} {configuration : FiniteContourConfiguration count}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ} {initial : MovingContourState count}

def externalSourceField
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (time : ℝ) (index : Fin count) : ℂ → ℂ :=
  Section6.finiteDomainSourceField (Finset.univ.erase index)
    (fun source => (trajectory.movingPatch source).domain time) configuration.density

theorem externalSourceField_eq_pointContours
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (index : Fin count) (position : ℂ) :
    trajectory.externalSourceField time index position =
      ∑ source ∈ Finset.univ.erase index, configuration.density source • pointContourVelocity
        (configuration.movingStatePhysicalContour (trajectory.curve time) source).val.1
        (configuration.movingStatePhysicalContour (trajectory.curve time) source).val.2.val.1 position (-Real.pi) Real.pi := by
  unfold externalSourceField Section6.finiteDomainSourceField
  apply Finset.sum_congr rfl
  intro source _
  rw [Section6.biotSavart_indicator_density_integral ((trajectory.movingPatch source).domain_isOpen time).measurableSet]
  have chordSmall : ‖(trajectory.movingPatch source).shape time - standardCircleBanach‖ < 2 / (3 * Real.pi) :=
    ((trajectory.admissible time).2.1 source).trans_lt (trajectory.shape_small.trans_le (min_le_right _ _))
  rw [(trajectory.movingPatch source).integral_domain_kernel_eq_pointContour time chordSmall position,
    trajectory.movingPatch_physicalContour_eq inside source]
  rfl

theorem movingStateExternalField_value
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (index : Fin count) (label : ℝ) :
    (configuration.movingStateExternalField (trajectory.curve time) index).val.1 label =
      (configuration.radius index)⁻¹ •
        (((configuration.movingStatePhase (trajectory.curve time) index : ℂ)⁻¹) *
          trajectory.externalSourceField time index
            ((configuration.movingStatePhysicalContour (trajectory.curve time) index).val.1 label)) := by
  rw [trajectory.externalSourceField_eq_pointContours inside index]
  let evaluation := contourLabelEvaluation label
  change evaluation (∑ source ∈ Finset.univ.erase index, _) = _
  rw [map_sum]
  simp only [Finset.smul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro source member
  rw [evaluation.map_smul]
  change (configuration.density source / configuration.radius index) •
    ((((configuration.movingStatePhase (trajectory.curve time) index)⁻¹ : Circle) : ℂ) *
      (extendedCrossContourVelocity (configuration.movingStatePhysicalContour (trajectory.curve time) index)
        (configuration.movingStatePhysicalContour (trajectory.curve time) source)).val.1 label) = _
  have shapeBound : shapeRadius ≤ 1 := (trajectory.shape_small.trans_le (min_le_left _ _)).le.trans (by norm_num)
  rw [extendedCrossContourVelocity_eq _ _ trajectory.gap_positive
    (configuration.movingStateAdmissible_physical_separated trajectory.gap_positive shapeBound
      (trajectory.admissible time) index source (Finset.ne_of_mem_erase member).symm),
    crossContourVelocityBanach_value]
  simp only [Complex.real_smul, Circle.coe_inv, Complex.ofReal_div, Complex.ofReal_inv]
  ring

def externalSpatialContourField
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (time : ℝ) (index : Fin count) (distance : Fin count → ℝ) (strain hessian : ℝ≥0)
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (separated : ∀ position ∈ Metric.closedBall ((trajectory.curve time).2.1 index) (4 * configuration.radius index),
      ∀ source ∈ Finset.univ.erase index, ∀ location ∈ (trajectory.movingPatch source).domain time,
      distance source ≤ ‖position - location‖)
    (strainBound : (∑ source ∈ Finset.univ.erase index,
      |configuration.density source| * volume.real ((trajectory.movingPatch source).domain time) /
        (2 * Real.pi * distance source ^ 2)) ≤ (strain : ℝ))
    (hessianBound : (∑ source ∈ Finset.univ.erase index,
      |configuration.density source| * volume.real ((trajectory.movingPatch source).domain time) /
        (Real.pi * distance source ^ 3)) ≤ (hessian : ℝ)) :
    SpatialContourField ((trajectory.curve time).2.1 index) (configuration.radius index) :=
  Section6.finiteDomainSpatialContourField (Finset.univ.erase index)
    (fun source => (trajectory.movingPatch source).domain time) configuration.density distance
    ((trajectory.curve time).2.1 index) (configuration.radius_pos index) strain hessian
    (fun source _ => ((trajectory.movingPatch source).domain_isOpen time).measurableSet)
    (fun source _ => ((trajectory.movingPatch source).domain_isBounded time).measure_lt_top)
    positive separated strainBound hessianBound

theorem movingStateExternalField_eq_rawRotatedCompose
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (index : Fin count)
    (source : SpatialContourField ((trajectory.curve time).2.1 index) (configuration.radius index))
    (fieldIdentity : source.field = trajectory.externalSourceField time index) :
    configuration.movingStateExternalField (trajectory.curve time) index =
      source.rawRotatedCompose ((trajectory.curve time).2.2 index)
        (configuration.movingStatePhase (trajectory.curve time) index) (configuration.radius_pos index)
        (configuration.movingStateAdmissible_shapes_bounded
          ((trajectory.shape_small.trans_le (min_le_left _ _)).le.trans (by norm_num)) (trajectory.admissible time) index) := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [trajectory.movingStateExternalField_value inside index label, source.rawRotatedCompose_value, fieldIdentity]
  rfl

theorem movingStateExternalField_gauge_norm_bound
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (index : Fin count)
    (distance : Fin count → ℝ) (strain hessian : ℝ≥0)
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (separated : ∀ position ∈ Metric.closedBall ((trajectory.curve time).2.1 index) (4 * configuration.radius index),
      ∀ source ∈ Finset.univ.erase index, ∀ location ∈ (trajectory.movingPatch source).domain time,
      distance source ≤ ‖position - location‖)
    (strainBound : (∑ source ∈ Finset.univ.erase index,
      |configuration.density source| * volume.real ((trajectory.movingPatch source).domain time) /
        (2 * Real.pi * distance source ^ 2)) ≤ (strain : ℝ))
    (hessianBound : (∑ source ∈ Finset.univ.erase index,
      |configuration.density source| * volume.real ((trajectory.movingPatch source).domain time) /
        (Real.pi * distance source ^ 3)) ≤ (hessian : ℝ))
    {constant : ℝ} (constantNonnegative : 0 ≤ constant)
    (centroidDerivativeBound : ‖fderiv ℝ contourCentroidFunctional ((trajectory.curve time).2.2 index)‖ ≤ constant) :
    ‖contourCentroidGaugeProjection ((trajectory.curve time).2.2 index)
      (configuration.movingStateExternalField (trajectory.curve time) index)‖ ≤
        (1 + constant) * (3 * (strain : ℝ) + 18 * configuration.radius index * (hessian : ℝ)) := by
  let source := trajectory.externalSpatialContourField time index distance strain hessian positive separated strainBound hessianBound
  have fieldIdentity : source.field = trajectory.externalSourceField time index := rfl
  have dataBound := configuration.movingStateAdmissible_shapes_bounded
    ((trajectory.shape_small.trans_le (min_le_left _ _)).le.trans (by norm_num)) (trajectory.admissible time) index
  have small : ‖(trajectory.curve time).2.2 index - standardCircleBanach‖ < 1 / 3 :=
    ((trajectory.admissible time).2.1 index).trans_lt (trajectory.shape_small.trans_le (min_le_left _ _))
  rw [trajectory.movingStateExternalField_eq_rawRotatedCompose inside index source fieldIdentity]
  exact source.gaugeProjection_rawRotatedCompose_norm_bound _ _ (configuration.radius_pos index) dataBound
    small constantNonnegative centroidDerivativeBound

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
