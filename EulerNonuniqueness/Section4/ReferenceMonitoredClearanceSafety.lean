import EulerNonuniqueness.Section4.ReferenceMonitoredContourImprovement
import EulerNonuniqueness.Section4.ReferenceCutoffSafety

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

theorem reference_clearance_monitor_strict_of_nonpositive_monitors
    {count : ℕ} (countPositive : 0 < count) {configuration : FiniteContourConfiguration (count * 4)}
    {shapeRadius gap margin backwardHorizon forwardHorizon : ℝ} {initial : MovingContourState (count * 4)}
    (trajectory : MovingCentroidGaugeTrajectory configuration 4 shapeRadius gap margin
      backwardHorizon forwardHorizon initial) (scales : Scales)
    (radiusIdentity : ∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1))
    (initialCircles : ∀ label, initial.2.2 label = standardCircleBanach)
    (shapePositive : 0 < shapeRadius) (marginPositive : 0 < margin)
    (marginShape : margin ≤ shapeRadius / 8) (marginUnit : margin ≤ 1 / 8)
    (marginSlack : ∀ first second : Fin count × Fin 4,
      gap + 4 * margin ≤ 4 * referencePairCutoffSlack scales first second)
    {time shapeStop : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon)
    (stopSmall : shapeStop ≤ shapeRadius / 2)
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (radiusSmall : ∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000)
    (bounds : ∀ monitor, referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop
      (trajectory.curve time) monitor ≤ 0) :
    referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop (trajectory.curve time) .clearance < 0 := by
  have decoded := trajectory.reference_paper_geometry_of_nonpositive_monitors scales initialCircles inside bounds
  have improved := reference_cutoff_margin_of_geometric_bounds countPositive scales configuration radiusIdentity
    shapePositive marginShape marginUnit marginSlack (trajectory.curve time)
    (fun index patch => (trajectory.patchCentroid_eq_curve_center initialCircles inside index patch).symm)
    (fun label => referenceMechanicalMonitor_center label (bounds (.center label)))
    (fun label => (referenceMechanicalMonitor_shape label (bounds (.shape label))).trans stopSmall)
    (fun index => (decoded.2.1 index).1) (fun index => (decoded.2.1 index).2.1)
    (fun index => (decoded.2.1 index).2.2.2.1) (fun index => (decoded.2.1 index).2.2.1)
    (fun receiver source different => (decoded.2.2 receiver source different).1) lengthSmall radiusSmall
  change margin - infDist (trajectory.curve time) (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ < 0
  linarith

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
