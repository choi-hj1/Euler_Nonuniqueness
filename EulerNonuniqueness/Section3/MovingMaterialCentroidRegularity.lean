import EulerNonuniqueness.Section3.MovingMaterialCentroidGeometry

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

local instance materialCentroidRegularityHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance materialCentroidRegularityC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

private theorem contDiffAt_one_of_continuous_velocity {Space : Type*} [NormedAddCommGroup Space]
    [NormedSpace ℝ Space] {path velocity : ℝ → Space} {left right time : ℝ}
    (velocityContinuous : Continuous velocity)
    (equation : ∀ current ∈ Ioo left right, HasDerivAt path (velocity current) current)
    (inside : time ∈ Ioo left right) : ContDiffAt ℝ 1 path time := by
  apply contDiffAt_one_iff.mpr
  refine ⟨fun current => (1 : ℝ →L[ℝ] ℝ).smulRight (velocity current), Ioo left right,
    isOpen_Ioo.mem_nhds inside, ?_, ?_⟩
  · exact (((ContinuousLinearMap.smulRightL ℝ ℝ Space) 1).continuous.comp velocityContinuous).continuousOn
  · intro current member
    exact (equation current member).hasFDerivAt

theorem MovingMaterialPatch.centroid_contDiffAt (path : MovingMaterialPatch) {time : ℝ}
    (inside : time ∈ Ioo path.initialTime path.finalTime) : ContDiffAt ℝ 1 path.centroid time := by
  have centerSmooth := contDiffAt_one_of_continuous_velocity path.centerVelocity_continuous
    (fun current _ => path.center_equation current) inside
  have phaseSmooth := contDiffAt_one_of_continuous_velocity path.phaseVelocity_continuous
    (fun current _ => path.phase_equation current) inside
  have shapeSmooth : ContDiffAt ℝ 1 path.shape time :=
    contDiffAt_one_of_continuous_velocity (Space := PeriodicC1HolderHalf)
      path.shapeVelocity_continuous path.shape_equation inside
  have centroidSmooth : ContDiffAt ℝ 1 (fun current => contourCentroidFunctional (path.shape current)) time :=
    (analyticAt_contourCentroidFunctional (path.shape time) (path.nearby time)).contDiffAt.comp time shapeSmooth
  have complexPhase : ContDiffAt ℝ 1 (fun current => (path.phase current : ℂ)) time :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp time phaseSmooth
  have rotationSmooth : ContDiffAt ℝ 1 (fun current => (Circle.exp (path.phase current) : ℂ)) time := by
    simpa only [Circle.coe_exp, mul_comm] using (complexPhase.mul contDiffAt_const).cexp
  have physical := centerSmooth.add ((rotationSmooth.mul centroidSmooth).const_smul path.radius)
  apply physical.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun current => path.centroid_eq_center_add_contourCentroid current

theorem MovingMaterialPatch.centroid_contDiffOn (path : MovingMaterialPatch) :
    ContDiffOn ℝ 1 path.centroid (Ioo path.initialTime path.finalTime) :=
  fun time inside => (path.centroid_contDiffAt inside).contDiffWithinAt

theorem MovingMaterialPatch.centroid_deriv_continuousOn (path : MovingMaterialPatch) :
    ContinuousOn (deriv path.centroid) (Ioo path.initialTime path.finalTime) := by
  intro time inside
  have derivativeContinuous : ContinuousAt (fderiv ℝ path.centroid) time :=
    ((path.centroid_contDiffAt inside).fderiv_right (m := 0) (by norm_num)).continuousAt
  exact ((ContinuousLinearMap.apply ℝ ℂ (1 : ℝ)).continuous.continuousAt.comp derivativeContinuous).continuousWithinAt

end EulerNonuniqueness.Paper
