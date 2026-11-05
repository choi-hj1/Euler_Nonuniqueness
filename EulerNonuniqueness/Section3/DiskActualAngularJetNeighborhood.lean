import EulerNonuniqueness.Section3.DiskNormalizedSpectralRelativeIncrement
import EulerNonuniqueness.Section3.MovingStrainAngularCorrectionDerivative
import EulerNonuniqueness.General.LocalRegularityNeighborhood
import EulerNonuniqueness.General.LocalC1LipschitzBounds
import EulerNonuniqueness.General.OperatorEvaluationContinuity

noncomputable section

open Filter Metric Set
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

local instance actualAngularJetNeighborhoodC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskPhysicalSpectralInverseDerivative_lipschitzNear_circle :
    EulerNonuniqueness.General.LipschitzNear diskPhysicalSpectralInverseDerivative standardCircleBanach := by
  obtain ⟨radius, positive, constant, one, _, difference⟩ :=
    diskPhysicalSpectralInverseDerivative_exists_uniform_pair_bounds
  refine ⟨⟨constant, by linarith⟩, closedBall standardCircleBanach radius, closedBall_mem_nhds _ positive, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro first firstInside final finalInside
  simpa only [dist_eq_norm] using difference first final
    (by simpa only [mem_closedBall, dist_eq_norm] using firstInside)
    (by simpa only [mem_closedBall, dist_eq_norm] using finalInside)

theorem diskPhysicalSpectralCoordinate_exists_actual_angular_jet_neighborhood :
    ∃ radius > 0, ∀ (curve velocity : ℝ → PeriodicC1HolderHalf) {left right time : ℝ},
      Continuous curve → Continuous velocity → time ∈ Ioo left right →
      (∀ current ∈ Ioo left right, HasDerivAt curve (velocity current) current) →
      ‖curve time - standardCircleBanach‖ < radius →
      ‖diskNeutralCLM (diskPhysicalSpectralCoordinate (curve time))‖ < 1 / 2 ∧
      ‖diskRelabelCurve (diskNeutralCLM (diskPhysicalSpectralCoordinate (curve time))) 1 - standardCircleBanach‖ < 1 / 3 ∧
      ‖diskRelabelCurve (diskNeutralCLM (diskPhysicalSpectralCoordinate (curve time))) 1 - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) ∧
      DifferentiableAt ℝ movingStrainAngularCoefficient (diskNeutralCLM (diskPhysicalSpectralCoordinate (curve time))) ∧
      ∃ nextLeft nextRight speed : ℝ, time ∈ Ioo nextLeft nextRight ∧ Ioo nextLeft nextRight ⊆ Ioo left right ∧
        (∀ current ∈ Ioo nextLeft nextRight,
          HasFDerivAt diskPhysicalSpectralCoordinate (diskPhysicalSpectralInverseDerivative (curve current)) (curve current)) ∧
        (∀ current ∈ Ioo nextLeft nextRight,
          HasDerivAt (fun position => diskNeutralCLM (diskPhysicalSpectralCoordinate (curve position)))
            (diskNeutralCLM (diskPhysicalSpectralInverseDerivative (curve current) (velocity current))) current) ∧
        (∀ current ∈ Ioo nextLeft nextRight,
          ‖diskRelabelCurve (diskNeutralCLM (diskPhysicalSpectralCoordinate (curve current))) 1‖ < 3 ∧
          ‖fderiv ℝ (fun parameter => diskRelabelCurve parameter 1)
              (diskNeutralCLM (diskPhysicalSpectralCoordinate (curve current)))
              (diskNeutralCLM (diskPhysicalSpectralInverseDerivative (curve current) (velocity current)))‖ ≤ speed) := by
  obtain ⟨derivativeRadius, derivativePositive, derivativeConstant, derivativeOne, _, derivativeBounds, _⟩ :=
    (EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_analyticAt (diskRelabelMap_analyticAt 0)).exists_uniform_derivative_ball
  have angularDifferentiable := movingStrainAngularCoefficient_hasLipschitzDerivativeNear.1
  have baseZero : diskRelabelCurve (0 : PeriodicC1HolderHalf) 1 = standardCircleBanach := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    rw [diskRelabelCurve_value]
    change Complex.exp ((1 : ℂ) * (Complex.I * 0)) * standardCircle label = standardCircle label
    simp
  have baseNear : ∀ᶠ angular in 𝓝 (0 : PeriodicC1HolderHalf),
      ‖angular‖ < 1 / 2 ∧ ‖angular‖ ≤ derivativeRadius ∧
      ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < 1 / 3 ∧
      ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) ∧
      ‖diskRelabelCurve angular 1‖ < 3 ∧ DifferentiableAt ℝ movingStrainAngularCoefficient angular := by
    have continuous := (diskRelabelMap_analyticAt 0).continuousAt
    have firstHalf : ∀ᶠ angular in 𝓝 (0 : PeriodicC1HolderHalf), ‖angular‖ < 1 / 2 :=
      continuous_norm.continuousAt.eventually (gt_mem_nhds (by norm_num : ‖(0 : PeriodicC1HolderHalf)‖ < (1 / 2 : ℝ)))
    have firstDerivative : ∀ᶠ angular in 𝓝 (0 : PeriodicC1HolderHalf), ‖angular‖ < derivativeRadius :=
      continuous_norm.continuousAt.eventually (gt_mem_nhds (by simpa only [norm_zero] using derivativePositive : ‖(0 : PeriodicC1HolderHalf)‖ < derivativeRadius))
    have first := firstHalf.and (firstDerivative.mono (fun _ small => small.le))
    have near := (continuous.sub_const standardCircleBanach).norm
    have second := near.eventually (gt_mem_nhds (by simpa only [baseZero, sub_self, norm_zero] using (by norm_num : (0 : ℝ) < 1 / 3)))
    have third := near.eventually (gt_mem_nhds (by simpa only [baseZero, sub_self, norm_zero] using
      (lt_min zero_lt_one (div_pos (by norm_num) (mul_pos (by norm_num) Real.pi_pos)) : (0 : ℝ) < min 1 (2 / (3 * Real.pi)))))
    have fourth := continuous.norm.eventually (gt_mem_nhds (by
      change ‖diskRelabelCurve (0 : PeriodicC1HolderHalf) 1‖ < 3
      rw [baseZero]
      linarith [standardCircleBanach_norm_bound]))
    simpa only [and_assoc] using first.and (second.and (third.and (fourth.and angularDifferentiable)))
  have angularContinuous : ContinuousAt
      (fun data => diskNeutralCLM (diskPhysicalSpectralCoordinate data)) standardCircleBanach :=
    diskNeutralCLM.continuous.continuousAt.comp diskPhysicalSpectralCoordinate_continuousAt_circle
  have angularZero : diskNeutralCLM (diskPhysicalSpectralCoordinate standardCircleBanach) = 0 := by
    rw [diskPhysicalSpectralCoordinate_circle, map_zero]
  have geometric : ∀ᶠ data in 𝓝 standardCircleBanach,
      HasFDerivAt diskPhysicalSpectralCoordinate (diskPhysicalSpectralInverseDerivative data) data ∧
      ContinuousAt diskPhysicalSpectralInverseDerivative data ∧
      ‖diskNeutralCLM (diskPhysicalSpectralCoordinate data)‖ < 1 / 2 ∧
      ‖diskNeutralCLM (diskPhysicalSpectralCoordinate data)‖ ≤ derivativeRadius ∧
      ‖diskRelabelCurve (diskNeutralCLM (diskPhysicalSpectralCoordinate data)) 1 - standardCircleBanach‖ < 1 / 3 ∧
      ‖diskRelabelCurve (diskNeutralCLM (diskPhysicalSpectralCoordinate data)) 1 - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) ∧
      ‖diskRelabelCurve (diskNeutralCLM (diskPhysicalSpectralCoordinate data)) 1‖ < 3 ∧
      DifferentiableAt ℝ movingStrainAngularCoefficient (diskNeutralCLM (diskPhysicalSpectralCoordinate data)) := by
    have pulled := angularContinuous.eventually (by simpa only [angularZero] using baseNear)
    filter_upwards [diskPhysicalSpectralCoordinate_eventually_inverse_derivative,
      diskPhysicalSpectralInverseDerivative_lipschitzNear_circle.eventually, pulled] with data inverse regular bounds
    exact ⟨inverse.2.1, regular.continuousAt, bounds⟩
  obtain ⟨radius, positive, valid⟩ := Metric.eventually_nhds_iff.mp geometric
  refine ⟨radius, positive, ?_⟩
  intro curve velocity left right time curveContinuous velocityContinuous inside equation small
  have atBase := valid (by simpa only [dist_eq_norm] using small)
  let angularVelocity := fun current => diskNeutralCLM (diskPhysicalSpectralInverseDerivative (curve current) (velocity current))
  have velocityAtBase : ContinuousAt angularVelocity time :=
    diskNeutralCLM.continuous.continuousAt.comp
      (EulerNonuniqueness.General.continuousAt_operator_evaluation
        (atBase.2.1.comp curveContinuous.continuousAt) velocityContinuous.continuousAt)
  have speedNear : ∀ᶠ current in 𝓝 time, ‖angularVelocity current‖ < ‖angularVelocity time‖ + 1 :=
    velocityAtBase.norm.eventually (gt_mem_nhds (lt_add_one _))
  have geometryNear := curveContinuous.continuousAt.eventually
    ((isOpen_ball.mem_nhds (by simpa only [mem_ball, dist_eq_norm] using small : curve time ∈ ball standardCircleBanach radius)))
  have intervalNear : ∀ᶠ current in 𝓝 time, current ∈ Ioo left right := Ioo_mem_nhds inside.1 inside.2
  obtain ⟨localRadius, localPositive, contained⟩ := Metric.eventually_nhds_iff.mp
    (intervalNear.and (geometryNear.and speedNear))
  have within (current : ℝ) (member : current ∈ Ioo (time - localRadius) (time + localRadius)) : dist current time < localRadius := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [member.1, member.2]
  have localGeometry (current : ℝ) (member : current ∈ Ioo (time - localRadius) (time + localRadius)) :=
    valid (by simpa only [mem_ball] using (contained (within current member)).2.1)
  refine ⟨atBase.2.2.1, atBase.2.2.2.2.1, atBase.2.2.2.2.2.1, atBase.2.2.2.2.2.2.2,
    time - localRadius, time + localRadius, derivativeConstant * (‖angularVelocity time‖ + 1),
    ⟨by linarith, by linarith⟩, (fun current member => (contained (within current member)).1),
    (fun current member => (localGeometry current member).1), ?_, ?_⟩
  · intro current member
    have actual := (diskNeutralCLM.hasFDerivAt.comp (curve current) (localGeometry current member).1).comp_hasDerivAt
      current (equation current (contained (within current member)).1)
    with_reducible_and_instances
      simpa only [Function.comp_def, ContinuousLinearMap.comp_apply] using actual
  · intro current member
    refine ⟨(localGeometry current member).2.2.2.2.2.2.1, ?_⟩
    have operator := derivativeBounds _ (by simpa only [sub_zero] using (localGeometry current member).2.2.2.1)
    have applied := (fderiv ℝ (fun parameter => diskRelabelCurve parameter 1)
      (diskNeutralCLM (diskPhysicalSpectralCoordinate (curve current)))).le_opNorm (angularVelocity current)
    exact applied.trans (mul_le_mul operator (contained (within current member)).2.2.le (norm_nonneg _)
      (by linarith : 0 ≤ derivativeConstant))

end EulerNonuniqueness.Paper
