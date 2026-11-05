import EulerNonuniqueness.Section3.MovingCentroidGaugeTrajectory

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingGaugeJointHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingGaugeJointC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem FiniteContourConfiguration.exists_jointly_continuous_movingCentroidGaugeTrajectories {count : ℕ}
    (configuration : FiniteContourConfiguration count) :
    ∃ shapeRadius > 0, shapeRadius < min (1 / 3) (2 / (3 * Real.pi)) ∧
      ∀ centerBound ≥ 0, ∀ gap > 0, ∀ margin > 0, ∀ backwardHorizon > 0, ∀ forwardHorizon > 0,
      ∃ trajectories : (initial : configuration.movingStateAdmissible centerBound shapeRadius gap) →
        MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial.val,
        Continuous (fun point : configuration.movingStateAdmissible centerBound shapeRadius gap × ℝ =>
          (trajectories point.1).curve point.2) := by
  obtain ⟨shapeRadius, shapePositive, shapeSmall, families⟩ :=
    configuration.exists_two_sided_moving_centroid_gauge_cutoff_family
  refine ⟨shapeRadius, shapePositive, shapeSmall, ?_⟩
  intro centerBound centerNonnegative gap gapPositive margin marginPositive backwardHorizon backwardPositive forwardHorizon forwardPositive
  obtain ⟨flow, fieldContinuous, initialIdentity, jointContinuous, equation, admissible⟩ :=
    families centerBound centerNonnegative gap gapPositive margin marginPositive backwardHorizon backwardPositive forwardHorizon forwardPositive
  let trajectories : (initial : configuration.movingStateAdmissible centerBound shapeRadius gap) →
      MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial.val :=
    fun initial => {
      backward_positive := backwardPositive
      forward_positive := forwardPositive
      shape_small := shapeSmall
      gap_positive := gapPositive
      curve := flow initial.val
      velocity := fun time => configuration.movingStateCutoffField centerBound shapeRadius gap margin (flow initial.val time)
      initial_identity := initialIdentity initial.val
      continuous := jointContinuous.comp (continuous_const.prodMk continuous_id)
      velocity_identity := fun _ => rfl
      velocity_continuous := fieldContinuous.comp (jointContinuous.comp (continuous_const.prodMk continuous_id))
      admissible := admissible initial.val initial.property
      equation := equation initial.val }
  refine ⟨trajectories, ?_⟩
  exact jointContinuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

namespace MovingCentroidGaugeTrajectory

variable {Parameter : Type*} [TopologicalSpace Parameter]
  {count : ℕ} {configuration : FiniteContourConfiguration count}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
  {initial : Parameter → MovingContourState count}

theorem joint_center_continuousOn_interior
    (trajectories : (parameter : Parameter) →
      MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon (initial parameter))
    (jointContinuous : Continuous (fun point : Parameter × ℝ => (trajectories point.1).curve point.2))
    (index : Fin count) :
    ContinuousOn (fun point : Parameter × ℝ => (trajectories point.1).center index point.2)
      {point | point.2 ∈ Ioo (-backwardHorizon) forwardHorizon} := by
  have stateCenter : ContinuousOn
      (fun point : Parameter × ℝ => ((trajectories point.1).curve point.2).2.1 index)
      {point | point.2 ∈ Ioo (-backwardHorizon) forwardHorizon} :=
    ((continuous_apply index).comp (continuous_fst.comp (continuous_snd.comp jointContinuous))).continuousOn
  apply stateCenter.congr
  intro point inside
  exact (trajectories point.1).center_eq_curve inside index

theorem joint_shape_continuous
    (trajectories : (parameter : Parameter) →
      MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon (initial parameter))
    (jointContinuous : Continuous (fun point : Parameter × ℝ => (trajectories point.1).curve point.2))
    (index : Fin count) :
    Continuous (fun point : Parameter × ℝ => ((trajectories point.1).movingPatch index).shape point.2) :=
  (continuous_apply index).comp (continuous_snd.comp (continuous_snd.comp jointContinuous))

end MovingCentroidGaugeTrajectory

end EulerNonuniqueness.Paper
