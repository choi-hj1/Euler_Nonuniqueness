import EulerNonuniqueness.Section4.ReferenceMonitoredContourImprovement

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

theorem reference_monitors_confined_of_paper_unstable_bound
    {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
    {shapeRadius gap margin : ℝ} {initial : MovingContourState (count * 4)}
    (trajectory : MovingCentroidGaugeTrajectory configuration 4 shapeRadius gap margin 1 3 initial)
    (scales : Scales) (initialCircles : ∀ label, initial.2.2 label = standardCircleBanach)
    {horizon shapeStop radius : ℝ} (beforeFinal : horizon < 3)
    (initialStrict : ∀ monitor,
      referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop initial monitor < 0)
    (bootstrap : ∀ terminal ∈ Icc 0 horizon,
      (∀ current ∈ Icc 0 terminal, ∀ index,
        |(movingReferenceShapeCoordinates scales (trajectory.curve current) index).1| ≤ radius) →
      ∀ current ∈ Icc 0 terminal, ∀ monitor,
        referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop (trajectory.curve current) monitor < 0)
    (unstableBound : ∀ current ∈ Icc 0 horizon, ∀ index,
      |unstableShape trajectory.movingFamily.patchMotion current index| ≤ radius) :
    ∀ current ∈ Icc 0 horizon, ∀ monitor,
      referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop (trajectory.curve current) monitor < 0 := by
  apply referenceMechanicalMonitor_confined_of_strict_prefix_improvement configuration scales shapeRadius gap margin shapeStop
    trajectory.continuous.continuousOn
  · simpa only [trajectory.initial_identity] using initialStrict
  intro terminal terminalInside closed _
  have regularizedBound (current : ℝ) (member : current ∈ Icc 0 terminal) (index : Fin count) :
      |(movingReferenceShapeCoordinates scales (trajectory.curve current) index).1| ≤ radius := by
    have globalMember : current ∈ Icc 0 horizon := ⟨member.1, member.2.trans terminalInside.2⟩
    have inside : current ∈ Ioo (-1 : ℝ) 3 :=
      ⟨by linarith [member.1], globalMember.2.trans_lt beforeFinal⟩
    have decoded := trajectory.reference_paper_geometry_of_nonpositive_monitors scales initialCircles inside (closed current member)
    have denominatorLower : scales.length (index.val + 1) ^ 2 / 2 ≤
        ‖positiveHalfDiagonal trajectory.movingFamily.patchMotion current index‖ ^ 2 := by
      have diagonalLower := (decoded.2.1 index).1
      dsimp only [diagonalDifference] at diagonalLower
      nlinarith [sq_nonneg ‖negativeHalfDiagonal trajectory.movingFamily.patchMotion current index‖]
    have agreement := trajectory.movingReferenceShapeCoordinates_eq_paper initialCircles scales inside index
      denominatorLower (decoded.2.1 index).2.2.2.2
    simpa only [agreement] using unstableBound current globalMember index
  exact bootstrap terminal terminalInside regularizedBound terminal ⟨terminalInside.1, le_rfl⟩

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
