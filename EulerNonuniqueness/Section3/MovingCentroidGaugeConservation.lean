import EulerNonuniqueness.Section3.MovingCentroidGaugeTrajectory
import EulerNonuniqueness.Section3.MovingMaterialCentroidGeometry
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingGaugeConservationHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingGaugeConservationC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

private theorem clm_real_smul_zero {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    (linear : Space →L[ℝ] ℂ) (direction : Space) (scalar : ℝ) (zero : linear direction = 0) :
    linear (scalar • direction) = 0 := by
  rw [map_smul, zero, smul_zero]

theorem contourCentroidFunctional_standardCircle_zero : contourCentroidFunctional standardCircleBanach = 0 := by
  have unit (label : ℝ) : standardCircleBanach.val.1 label * star (standardCircleBanach.val.1 label) = (1 : ℂ) := by
    change standardCircle label * star (standardCircle label) = 1
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, standardCircle_norm]
    norm_num
  have momentZero : contourPolynomialMoment 1 standardCircleBanach = 0 := by
    rw [contourPolynomialMoment_eq_integral]
    have integrand : (fun label => standardCircleBanach.val.1 label ^ 1 * star (standardCircleBanach.val.1 label) *
        standardCircleBanach.val.2.val.1 label) = standardCircleBanach.val.2.val.1 := by
      funext label
      rw [pow_one, unit, one_mul]
    rw [integrand, contour_tangent_integral_zero, mul_zero]
  rw [contourCentroidFunctional, momentZero, zero_div]

namespace MovingCentroidGaugeTrajectory

variable {count : ℕ} {configuration : FiniteContourConfiguration count}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ} {initial : MovingContourState count}

theorem contourCentroid_hasDerivAt_zero
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (index : Fin count) :
    HasDerivAt (fun current => contourCentroidFunctional ((trajectory.curve current).2.2 index)) 0 time := by
  have small : ‖(trajectory.curve time).2.2 index - standardCircleBanach‖ < 1 / 3 :=
    ((trajectory.admissible time).2.1 index).trans_lt (trajectory.shape_small.trans_le (min_le_left _ _))
  have centroidDerivative : HasFDerivAt contourCentroidFunctional
      (fderiv ℝ contourCentroidFunctional ((trajectory.curve time).2.2 index)) ((trajectory.curve time).2.2 index) :=
    (analyticAt_contourCentroidFunctional _ small).differentiableAt.hasFDerivAt
  have actualZero : (fderiv ℝ contourCentroidFunctional ((trajectory.curve time).2.2 index)) ((trajectory.velocity time).2.2 index) = 0 := by
    rw [trajectory.velocity_identity]
    change (fderiv ℝ contourCentroidFunctional ((trajectory.curve time).2.2 index))
      (EulerNonuniqueness.General.distanceFieldCutoff
        (configuration.movingStateAdmissible centerBound shapeRadius gap) margin (trajectory.curve time) •
          contourCentroidGaugeProjection ((trajectory.curve time).2.2 index)
            (configuration.movingStateRawField (trajectory.curve time) index)) = 0
    exact clm_real_smul_zero (Space := PeriodicC1HolderHalf)
      (fderiv ℝ contourCentroidFunctional ((trajectory.curve time).2.2 index))
      (contourCentroidGaugeProjection ((trajectory.curve time).2.2 index)
        (configuration.movingStateRawField (trajectory.curve time) index))
      (EulerNonuniqueness.General.distanceFieldCutoff
        (configuration.movingStateAdmissible centerBound shapeRadius gap) margin (trajectory.curve time))
      (contourCentroidGaugeProjection_centroid_zero ((trajectory.curve time).2.2 index)
        (configuration.movingStateRawField (trajectory.curve time) index) small)
  have chain := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := PeriodicC1HolderHalf) (E := ℂ)
    time centroidDerivative (trajectory.shape_component_hasDerivAt inside index)
  simpa only [Function.comp_def, actualZero] using chain

theorem contourCentroid_conserved
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (index : Fin count) :
    contourCentroidFunctional ((trajectory.curve time).2.2 index) = contourCentroidFunctional (initial.2.2 index) := by
  have differentiable : DifferentiableOn ℝ (fun current => contourCentroidFunctional ((trajectory.curve current).2.2 index))
      (Ioo (-backwardHorizon) forwardHorizon) :=
    fun _ currentInside => (trajectory.contourCentroid_hasDerivAt_zero currentInside index).differentiableAt.differentiableWithinAt
  have derivativeZero : (Ioo (-backwardHorizon) forwardHorizon).EqOn
      (deriv (fun current => contourCentroidFunctional ((trajectory.curve current).2.2 index))) 0 :=
    fun _ currentInside => (trajectory.contourCentroid_hasDerivAt_zero currentInside index).deriv
  have initialInside : (0 : ℝ) ∈ Ioo (-backwardHorizon) forwardHorizon :=
    ⟨neg_neg_of_pos trajectory.backward_positive, trajectory.forward_positive⟩
  have conserved := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo differentiable derivativeZero inside initialInside
  simpa only [trajectory.initial_identity] using conserved

theorem movingPatch_centroid_eq_center
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (initialCentered : ∀ index, contourCentroidFunctional (initial.2.2 index) = 0)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (index : Fin count) :
    (trajectory.movingPatch index).centroid time = trajectory.center index time := by
  apply (trajectory.movingPatch index).centroid_eq_center_of_contourCentroid_zero time
  exact (trajectory.contourCentroid_conserved inside index).trans (initialCentered index)

theorem movingPatch_centroid_eq_center_of_initial_circles
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (initialCircle : ∀ index, initial.2.2 index = standardCircleBanach)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (index : Fin count) :
    (trajectory.movingPatch index).centroid time = trajectory.center index time := by
  apply trajectory.movingPatch_centroid_eq_center _ inside index
  intro patch
  rw [initialCircle patch, contourCentroidFunctional_standardCircle_zero]

end MovingCentroidGaugeTrajectory

end EulerNonuniqueness.Paper
