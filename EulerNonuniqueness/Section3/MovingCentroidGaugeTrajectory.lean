import EulerNonuniqueness.Section3.MovingCentroidGaugeTwoSidedFlow
import EulerNonuniqueness.Section3.MovingMaterialPatch
import EulerNonuniqueness.Section3.FiniteMovingPatchFamily
import EulerNonuniqueness.General.ODEPrimitiveExtension
import EulerNonuniqueness.Section3.MovingContourStateProjections

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingGaugeTrajectoryHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingGaugeTrajectoryC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

structure MovingCentroidGaugeTrajectory {count : ℕ} (configuration : FiniteContourConfiguration count)
    (centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ) (initial : MovingContourState count) where
  backward_positive : 0 < backwardHorizon
  forward_positive : 0 < forwardHorizon
  shape_small : shapeRadius < min (1 / 3) (2 / (3 * Real.pi))
  gap_positive : 0 < gap
  curve : ℝ → MovingContourState count
  velocity : ℝ → MovingContourState count
  initial_identity : curve 0 = initial
  continuous : Continuous curve
  velocity_identity : ∀ time, velocity time = configuration.movingStateCutoffField centerBound shapeRadius gap margin (curve time)
  velocity_continuous : Continuous velocity
  admissible : ∀ time, curve time ∈ configuration.movingStateAdmissible centerBound shapeRadius gap
  equation : ∀ time ∈ Ioo (-backwardHorizon) forwardHorizon,
    HasDerivAt curve (velocity time) time

theorem FiniteContourConfiguration.exists_movingCentroidGaugeTrajectory {count : ℕ}
    (configuration : FiniteContourConfiguration count) :
    ∃ shapeRadius > 0, shapeRadius < min (1 / 3) (2 / (3 * Real.pi)) ∧
      ∀ centerBound ≥ 0, ∀ gap > 0, ∀ margin > 0, ∀ backwardHorizon > 0, ∀ forwardHorizon > 0,
      ∀ initial ∈ configuration.movingStateAdmissible centerBound shapeRadius gap,
        Nonempty (MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial) := by
  obtain ⟨shapeRadius, shapePositive, shapeSmall, families⟩ := configuration.exists_two_sided_moving_centroid_gauge_cutoff_family
  refine ⟨shapeRadius, shapePositive, shapeSmall, ?_⟩
  intro centerBound centerNonnegative gap gapPositive margin marginPositive backwardHorizon backwardPositive forwardHorizon forwardPositive initial initialInside
  obtain ⟨flow, fieldContinuous, initialIdentity, jointContinuous, equation, admissible⟩ :=
    families centerBound centerNonnegative gap gapPositive margin marginPositive backwardHorizon backwardPositive forwardHorizon forwardPositive
  refine ⟨⟨backwardPositive, forwardPositive, shapeSmall, gapPositive, flow initial,
    (fun time => configuration.movingStateCutoffField centerBound shapeRadius gap margin (flow initial time)), initialIdentity initial,
    jointContinuous.comp (continuous_const.prodMk continuous_id), (fun _ => rfl), ?_, admissible initial initialInside, equation initial⟩⟩
  exact fieldContinuous.comp (jointContinuous.comp (continuous_const.prodMk continuous_id))

namespace MovingCentroidGaugeTrajectory

variable {count : ℕ} {configuration : FiniteContourConfiguration count}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ} {initial : MovingContourState count}

theorem clock_component_hasDerivAt
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) :
    HasDerivAt (fun current => (trajectory.curve current).1) (trajectory.velocity time).1 time := by
  have linear : HasFDerivAt (movingContourStateClockCLM count) (movingContourStateClockCLM count) (trajectory.curve time) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := MovingContourState count) (F := ℝ) (movingContourStateClockCLM count)
  simpa only [Function.comp_def] using HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ)
    (F := MovingContourState count) (E := ℝ) (f := trajectory.curve) time linear (trajectory.equation time inside)

theorem center_component_hasDerivAt
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (index : Fin count) :
    HasDerivAt (fun current => (trajectory.curve current).2.1 index) ((trajectory.velocity time).2.1 index) time := by
  have linear : HasFDerivAt (movingContourStateCenterCLM count index) (movingContourStateCenterCLM count index) (trajectory.curve time) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := MovingContourState count) (F := ℂ) (movingContourStateCenterCLM count index)
  simpa only [Function.comp_def] using HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ)
    (F := MovingContourState count) (E := ℂ) (f := trajectory.curve) time linear (trajectory.equation time inside)

theorem shape_component_hasDerivAt
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (index : Fin count) :
    HasDerivAt (fun current => (trajectory.curve current).2.2 index) ((trajectory.velocity time).2.2 index) time := by
  have linear : HasFDerivAt (movingContourStateShapeCLM count index) (movingContourStateShapeCLM count index) (trajectory.curve time) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := MovingContourState count) (F := PeriodicC1HolderHalf) (movingContourStateShapeCLM count index)
  simpa only [Function.comp_def] using HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ)
    (F := MovingContourState count) (E := PeriodicC1HolderHalf) (f := trajectory.curve) time linear (trajectory.equation time inside)

def clock (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial) : ℝ → ℝ :=
  EulerNonuniqueness.General.odePrimitiveExtension (fun time => (trajectory.curve time).1) (fun time => (trajectory.velocity time).1)

def center (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (index : Fin count) : ℝ → ℂ :=
  EulerNonuniqueness.General.odePrimitiveExtension (fun time => (trajectory.curve time).2.1 index)
    (fun time => (trajectory.velocity time).2.1 index)

theorem clock_hasDerivAt
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial) (time : ℝ) :
    HasDerivAt trajectory.clock (trajectory.velocity time).1 time :=
  EulerNonuniqueness.General.odePrimitiveExtension_hasDerivAt _ _ (continuous_fst.comp trajectory.velocity_continuous) time

theorem center_hasDerivAt
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (index : Fin count) (time : ℝ) :
    HasDerivAt (trajectory.center index) ((trajectory.velocity time).2.1 index) time :=
  EulerNonuniqueness.General.odePrimitiveExtension_hasDerivAt _ _
    ((continuous_apply index).comp (continuous_fst.comp (continuous_snd.comp trajectory.velocity_continuous))) time

theorem clock_eq_curve
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) : trajectory.clock time = (trajectory.curve time).1 :=
  EulerNonuniqueness.General.odePrimitiveExtension_eq_on_interior _ _ (continuous_fst.comp trajectory.velocity_continuous)
    (neg_neg_of_pos trajectory.backward_positive) trajectory.forward_positive
    (fun _ currentInside => trajectory.clock_component_hasDerivAt currentInside) inside

theorem center_eq_curve
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (index : Fin count) :
    trajectory.center index time = (trajectory.curve time).2.1 index :=
  EulerNonuniqueness.General.odePrimitiveExtension_eq_on_interior _ _
    ((continuous_apply index).comp (continuous_fst.comp (continuous_snd.comp trajectory.velocity_continuous)))
    (neg_neg_of_pos trajectory.backward_positive) trajectory.forward_positive
    (fun _ currentInside => trajectory.center_component_hasDerivAt currentInside index) inside

def movingPatch
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (index : Fin count) : MovingMaterialPatch where
  radius := configuration.radius index
  radius_positive := configuration.radius_pos index
  initialTime := -backwardHorizon
  finalTime := forwardHorizon
  time_order := by linarith [trajectory.backward_positive, trajectory.forward_positive]
  center := trajectory.center index
  centerVelocity := fun time => (trajectory.velocity time).2.1 index
  phase := fun time => (configuration.density index / 2) * trajectory.clock time
  phaseVelocity := fun time => (configuration.density index / 2) * (trajectory.velocity time).1
  shape := fun time => (trajectory.curve time).2.2 index
  shapeVelocity := fun time => (trajectory.velocity time).2.2 index
  center_continuous := continuous_iff_continuousAt.mpr fun time => (trajectory.center_hasDerivAt index time).continuousAt
  centerVelocity_continuous := (continuous_apply index).comp (continuous_fst.comp (continuous_snd.comp trajectory.velocity_continuous))
  phase_continuous := continuous_const.mul (continuous_iff_continuousAt.mpr fun time => (trajectory.clock_hasDerivAt time).continuousAt)
  phaseVelocity_continuous := continuous_const.mul (continuous_fst.comp trajectory.velocity_continuous)
  shape_continuous := (continuous_apply index).comp (continuous_snd.comp (continuous_snd.comp trajectory.continuous))
  shapeVelocity_continuous := (continuous_apply index).comp (continuous_snd.comp (continuous_snd.comp trajectory.velocity_continuous))
  center_equation := trajectory.center_hasDerivAt index
  phase_equation := fun time => (trajectory.clock_hasDerivAt time).const_mul (configuration.density index / 2)
  shape_equation := fun _ inside => trajectory.shape_component_hasDerivAt inside index
  nearby := fun time => ((trajectory.admissible time).2.1 index).trans_lt (trajectory.shape_small.trans_le (min_le_left _ _))

def movingFamily
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial) :
    FiniteMovingPatchFamily count where
  patch := trajectory.movingPatch
  density := configuration.density

end MovingCentroidGaugeTrajectory

end EulerNonuniqueness.Paper
