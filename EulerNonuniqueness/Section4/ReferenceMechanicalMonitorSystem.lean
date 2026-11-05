import EulerNonuniqueness.Section4.MovingReferenceMechanicalMonitors
import EulerNonuniqueness.Section3.MovingContourCutoffMargin
import EulerNonuniqueness.General.StrictPrefixBootstrap

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance mechanicalMonitorHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance mechanicalMonitorC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph
local instance mechanicalMonitorC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

inductive ReferenceMechanicalIndex (count : ℕ)
  | clearance
  | shape (label : Fin (count * 4))
  | diagonal (index : Fin count)
  | asymmetry (index : Fin count)
  | radial (index : Fin count)
  | branch (index : Fin count)
  | pair (receiver source : Fin count)
  | center (label : Fin (count * 4))
  deriving DecidableEq, Fintype

instance (count : ℕ) : Nonempty (ReferenceMechanicalIndex count) := ⟨.clearance⟩

def movingReferencePositiveDiagonal {count : ℕ} (state : MovingContourState (count * 4)) (index : Fin count) : ℂ :=
  (state.2.1 (finProdFinEquiv (index, 0)) - state.2.1 (finProdFinEquiv (index, 1))) / 2

def movingReferenceNegativeDiagonal {count : ℕ} (state : MovingContourState (count * 4)) (index : Fin count) : ℂ :=
  (state.2.1 (finProdFinEquiv (index, 2)) - state.2.1 (finProdFinEquiv (index, 3))) / 2

def movingReferenceDiagonalDifference {count : ℕ} (state : MovingContourState (count * 4)) (index : Fin count) : ℝ :=
  ‖movingReferencePositiveDiagonal state index‖ ^ 2 - ‖movingReferenceNegativeDiagonal state index‖ ^ 2

def movingReferenceAsymmetry {count : ℕ} (state : MovingContourState (count * 4)) (index : Fin count) : ℂ :=
  (state.2.1 (finProdFinEquiv (index, 0)) + state.2.1 (finProdFinEquiv (index, 1)) -
    state.2.1 (finProdFinEquiv (index, 2)) - state.2.1 (finProdFinEquiv (index, 3))) / 4

def movingReferenceCenter {count : ℕ} (state : MovingContourState (count * 4)) (index : Fin count) : ℂ :=
  (∑ patch : Fin 4, state.2.1 (finProdFinEquiv (index, patch))) / 4

def referenceMechanicalMonitor {count : ℕ} (configuration : FiniteContourConfiguration (count * 4))
    (scales : Scales) (shapeRadius gap margin shapeStop : ℝ)
    (state : MovingContourState (count * 4)) : ReferenceMechanicalIndex count → ℝ
  | .clearance => margin - infDist state (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ
  | .shape label => ‖state.2.2 label - standardCircleBanach‖ - shapeStop
  | .diagonal index => |movingReferenceDiagonalDifference state index / scales.length (index.val + 1) ^ 2 - 1| - 1 / 2
  | .asymmetry index => ‖movingReferenceAsymmetry state index‖ / scales.length (index.val + 1) - 1 / 64
  | .radial index => |movingReferenceRadialObservable scales state index| - 1 / 2
  | .branch index => 1 / 16 - movingReferenceRatioImaginary scales state index
  | .pair receiver source => if receiver = source then -1 else
      ‖(movingReferenceCenter state receiver - movingReferenceCenter state source) -
        ((scales.location (receiver.val + 1) : ℂ) - (scales.location (source.val + 1) : ℂ))‖ -
        |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2
  | .center label => ‖state.2.1 label‖ - 3

theorem referenceMechanicalMonitor_continuous {count : ℕ}
    (configuration : FiniteContourConfiguration (count * 4)) (scales : Scales)
    (shapeRadius gap margin shapeStop : ℝ) (monitor : ReferenceMechanicalIndex count) :
    Continuous (fun state : MovingContourState (count * 4) =>
      referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop state monitor) := by
  have centerContinuous (label : Fin (count * 4)) :
      Continuous (fun state : MovingContourState (count * 4) => state.2.1 label) :=
    (continuous_apply label).comp (continuous_fst.comp continuous_snd)
  have shapeContinuous (label : Fin (count * 4)) :
      Continuous (fun state : MovingContourState (count * 4) => state.2.2 label) :=
    (continuous_apply label).comp (continuous_snd.comp continuous_snd)
  have positiveContinuous (index : Fin count) : Continuous (fun state : MovingContourState (count * 4) =>
      movingReferencePositiveDiagonal state index) :=
    ((centerContinuous _).sub (centerContinuous _)).div_const 2
  have negativeContinuous (index : Fin count) : Continuous (fun state : MovingContourState (count * 4) =>
      movingReferenceNegativeDiagonal state index) :=
    ((centerContinuous _).sub (centerContinuous _)).div_const 2
  have averageContinuous (index : Fin count) : Continuous (fun state : MovingContourState (count * 4) =>
      movingReferenceCenter state index) := by
    exact (continuous_finset_sum _ (fun patch _ => centerContinuous (finProdFinEquiv (index, patch)))).div_const 4
  cases monitor with
  | clearance => exact continuous_const.sub (continuous_infDist_pt _)
  | shape label => exact ((shapeContinuous label).sub continuous_const).norm.sub continuous_const
  | diagonal index =>
      exact ((((positiveContinuous index).norm.pow 2).sub ((negativeContinuous index).norm.pow 2)).div_const _
        |>.sub continuous_const).abs.sub continuous_const
  | asymmetry index =>
      exact (((((centerContinuous _).add (centerContinuous _)).sub (centerContinuous _)).sub
        (centerContinuous _)).div_const 4).norm.div_const _ |>.sub continuous_const
  | radial index => exact (movingReferenceRadialObservable_continuous scales index).abs.sub continuous_const
  | branch index => exact continuous_const.sub (movingReferenceRatioImaginary_continuous scales index)
  | pair receiver source =>
      by_cases same : receiver = source
      · simpa only [referenceMechanicalMonitor, same, if_true] using (continuous_const : Continuous
          (fun _ : MovingContourState (count * 4) => (-1 : ℝ)))
      · simpa only [referenceMechanicalMonitor, same, if_false] using
          (((averageContinuous receiver).sub (averageContinuous source)).sub continuous_const).norm.sub continuous_const
  | center label => exact (centerContinuous label).norm.sub continuous_const

namespace MovingCentroidGaugeTrajectory

theorem movingReferenceGeometricObservables_eq_paper {count : ℕ}
    {configuration : FiniteContourConfiguration (count * 4)}
    {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
    {initial : MovingContourState (count * 4)}
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial)
    (initialCircles : ∀ label, initial.2.2 label = standardCircleBanach)
    {time : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (index : Fin count) :
    movingReferenceDiagonalDifference (trajectory.curve time) index = diagonalDifference trajectory.movingFamily.patchMotion time index ∧
    movingReferenceAsymmetry (trajectory.curve time) index = centroidAsymmetry trajectory.movingFamily.patchMotion time index ∧
    movingReferenceCenter (trajectory.curve time) index = quadrupoleCenter trajectory.movingFamily.patchMotion time index := by
  have centers := trajectory.patchCentroid_eq_curve_center initialCircles inside index
  constructor
  · simp only [movingReferenceDiagonalDifference, movingReferencePositiveDiagonal, movingReferenceNegativeDiagonal,
      diagonalDifference, positiveHalfDiagonal, negativeHalfDiagonal, centers]
  constructor
  · simp only [movingReferenceAsymmetry, centroidAsymmetry, centers]
  · simp only [movingReferenceCenter, quadrupoleCenter, centers]

end MovingCentroidGaugeTrajectory

theorem referenceMechanicalMonitor_confined_of_strict_prefix_improvement {count : ℕ}
    (configuration : FiniteContourConfiguration (count * 4)) (scales : Scales)
    (shapeRadius gap margin shapeStop : ℝ) {curve : ℝ → MovingContourState (count * 4)} {horizon : ℝ}
    (continuous : ContinuousOn curve (Icc 0 horizon))
    (initial : ∀ monitor, referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop (curve 0) monitor < 0)
    (improve : ∀ time ∈ Icc 0 horizon,
      (∀ current ∈ Icc 0 time, ∀ monitor,
        referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop (curve current) monitor ≤ 0) →
      (∀ current ∈ Ico 0 time, ∀ monitor,
        referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop (curve current) monitor < 0) →
      ∀ monitor, referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop (curve time) monitor < 0) :
    ∀ time ∈ Icc 0 horizon, ∀ monitor,
      referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop (curve time) monitor < 0 := by
  apply EulerNonuniqueness.General.finite_strictly_negative_of_strict_prefix_improvement
    (fun monitor => (referenceMechanicalMonitor_continuous configuration scales shapeRadius gap margin shapeStop monitor).comp_continuousOn continuous)
    initial improve

end EulerNonuniqueness.Paper
