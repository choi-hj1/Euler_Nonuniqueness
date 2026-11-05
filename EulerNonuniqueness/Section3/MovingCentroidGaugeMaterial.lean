import EulerNonuniqueness.Section3.MovingCentroidGaugeTrajectory
import EulerNonuniqueness.Section3.MovingMaterialPatchBiotSavart

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingGaugeMaterialHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingGaugeMaterialC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

variable {count : ℕ} {configuration : FiniteContourConfiguration count}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ} {initial : MovingContourState count}

def configurationAt
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (time : ℝ) : FiniteContourConfiguration count :=
  configuration.atMovingState (trajectory.curve time)
    (configuration.movingStateAdmissible_centers_separated trajectory.gap_positive (trajectory.admissible time))

theorem movingPatch_physicalContour_eq
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (index : Fin count) :
    (trajectory.movingPatch index).physicalContour time =
      (trajectory.configurationAt time).phasedPhysicalContour (configuration.movingStatePhase (trajectory.curve time))
        (trajectory.curve time).2.2 index := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change trajectory.center index time + configuration.radius index •
      ((Circle.exp ((configuration.density index / 2) * trajectory.clock time) : ℂ) * ((trajectory.curve time).2.2 index).val.1 label) = _
  rw [trajectory.center_eq_curve inside index, trajectory.clock_eq_curve inside]
  rfl

theorem movingPatch_boundary_eq
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (index : Fin count) (label : ℝ) :
    (trajectory.movingPatch index).boundary time label =
      ((trajectory.configurationAt time).phasedPhysicalContour (configuration.movingStatePhase (trajectory.curve time))
        (trajectory.curve time).2.2 index).val.1 label := by
  rw [← MovingMaterialPatch.physicalContour_value, trajectory.movingPatch_physicalContour_eq inside index]

theorem movingFamily_biotSavart
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (position : ℂ) :
    biotSavart (trajectory.movingFamily.vorticity time) position =
      ∑ index, configuration.density index • pointContourVelocity
        ((trajectory.configurationAt time).phasedPhysicalContour (configuration.movingStatePhase (trajectory.curve time)) (trajectory.curve time).2.2 index).val.1
        ((trajectory.configurationAt time).phasedPhysicalContour (configuration.movingStatePhase (trajectory.curve time)) (trajectory.curve time).2.2 index).val.2.val.1
        position (-Real.pi) Real.pi := by
  rw [trajectory.movingFamily.biotSavart_eq_sum_physical_contours time
    (fun index => ((trajectory.admissible time).2.1 index).trans_lt (trajectory.shape_small.trans_le (min_le_right _ _))) position]
  apply Finset.sum_congr rfl
  intro index _member
  change configuration.density index • pointContourVelocity ((trajectory.movingPatch index).physicalContour time).val.1
    ((trajectory.movingPatch index).physicalContour time).val.2.val.1 position (-Real.pi) Real.pi = _
  rw [trajectory.movingPatch_physicalContour_eq inside index]

theorem velocity_eq_uncut_of_margin
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (marginPositive : 0 < margin) (time : ℝ)
    (safe : margin ≤ infDist (trajectory.curve time) (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) :
    trajectory.velocity time = configuration.movingStateVectorField (trajectory.curve time) := by
  rw [trajectory.velocity_identity, FiniteContourConfiguration.movingStateCutoffField,
    EulerNonuniqueness.General.distanceFieldCutoff_one _ marginPositive (trajectory.curve time) safe, one_smul]

theorem movingPatch_boundaryVelocity_eq_phasedVectorField
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (marginPositive : 0 < margin) {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon)
    (safe : margin ≤ infDist (trajectory.curve time) (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ)
    (index : Fin count) (label : ℝ) :
    (trajectory.movingPatch index).boundaryVelocity time label =
      configuration.radius index • ((configuration.movingStatePhase (trajectory.curve time) index : ℂ) *
        ((trajectory.configurationAt time).phasedVectorField (configuration.movingStatePhase (trajectory.curve time))
          (trajectory.curve time).2.2 index).val.1 label) := by
  have velocityIdentity := trajectory.velocity_eq_uncut_of_margin marginPositive time safe
  have clockVelocity : (configuration.movingStateVectorField (trajectory.curve time)).1 = (1 : ℝ) := rfl
  change (trajectory.velocity time).2.1 index + configuration.radius index •
      ((Complex.I * ((configuration.density index / 2) * (trajectory.velocity time).1 : ℝ)) *
        (Circle.exp ((configuration.density index / 2) * trajectory.clock time) : ℂ) * ((trajectory.curve time).2.2 index).val.1 label +
        (Circle.exp ((configuration.density index / 2) * trajectory.clock time) : ℂ) * ((trajectory.velocity time).2.2 index).val.1 label) = _
  rw [velocityIdentity, clockVelocity, mul_one, trajectory.clock_eq_curve inside]
  have algebra : (configuration.movingStateVectorField (trajectory.curve time)).2.1 index + configuration.radius index •
      ((Complex.I * (configuration.density index / 2 : ℝ)) * (configuration.movingStatePhase (trajectory.curve time) index : ℂ) *
          ((trajectory.curve time).2.2 index).val.1 label +
        (configuration.movingStatePhase (trajectory.curve time) index : ℂ) *
          ((configuration.movingStateVectorField (trajectory.curve time)).2.2 index).val.1 label) =
      (configuration.movingStateVectorField (trajectory.curve time)).2.1 index + configuration.radius index •
        ((configuration.movingStatePhase (trajectory.curve time) index : ℂ) *
          (((Complex.I * (configuration.density index / 2 : ℝ)) * ((trajectory.curve time).2.2 index).val.1 label) +
            ((configuration.movingStateVectorField (trajectory.curve time)).2.2 index).val.1 label)) := by
    simp only [Complex.real_smul]
    ring
  simp only [FiniteContourConfiguration.movingStatePhase] at algebra
  rw [algebra]
  exact configuration.movingStateVectorField_physical_velocity (trajectory.curve time)
    (configuration.movingStateAdmissible_centers_separated trajectory.gap_positive (trajectory.admissible time)) index label

theorem movingFamily_material_equation_of_margin
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (marginPositive : 0 < margin) {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon)
    (safe : margin ≤ infDist (trajectory.curve time) (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ)
    (index : Fin count) (label : ℝ) :
    (trajectory.movingFamily.patch index).boundaryVelocity time label =
      biotSavart (trajectory.movingFamily.vorticity time) ((trajectory.movingFamily.patch index).boundary time label) := by
  rw [show trajectory.movingFamily.patch index = trajectory.movingPatch index from rfl,
    trajectory.movingPatch_boundaryVelocity_eq_phasedVectorField marginPositive inside safe index label,
    trajectory.movingPatch_boundary_eq inside index label, trajectory.movingFamily_biotSavart inside]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ index)]
  exact (trajectory.configurationAt time).phased_physical_vectorField_label_value
    (configuration.movingStatePhase (trajectory.curve time)) (trajectory.curve time).2.2
    (fun source => ((trajectory.admissible time).2.1 source).trans_lt trajectory.shape_small)
    (fun source => configuration.movingStateAdmissible_shapes_bounded
      ((trajectory.shape_small.trans_le (min_le_left _ _)).trans (by norm_num)).le (trajectory.admissible time) source) index label

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
