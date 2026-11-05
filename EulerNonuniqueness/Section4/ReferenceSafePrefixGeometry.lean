import EulerNonuniqueness.Section4.ReferenceCentroidFieldGeometry
import EulerNonuniqueness.Section3.MovingCentroidGaugeEuler

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

theorem reference_geometry_of_safe_prefix
    {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
    {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
    {initial : MovingContourState (count * 4)}
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial) (scales : Scales)
    (densityIdentity : ∀ index patch, configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (radiusIdentity : ∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1))
    (initialCircles : ∀ index, initial.2.2 index = standardCircleBanach)
    (marginPositive : 0 < margin) {terminal : ℝ} (terminalNonnegative : 0 ≤ terminal)
    (beforeFinal : terminal < forwardHorizon)
    (safe : ∀ current ∈ Icc 0 terminal, margin ≤ infDist (trajectory.curve current)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (radiusSmall : ∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000)
    (differenceLower : ∀ current ∈ Icc 0 terminal, ∀ index,
      scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference trajectory.movingFamily.patchMotion current index)
    (differenceUpper : ∀ current ∈ Icc 0 terminal, ∀ index,
      diagonalDifference trajectory.movingFamily.patchMotion current index ≤ 2 * scales.length (index.val + 1) ^ 2)
    (radialSmall : ∀ current ∈ Icc 0 terminal, ∀ index,
      |radialShape trajectory.movingFamily.patchMotion current index| ≤ 1 / 2)
    (asymmetrySmall : ∀ current ∈ Icc 0 terminal, ∀ index,
      ‖centroidAsymmetry trajectory.movingFamily.patchMotion current index‖ ≤ scales.length (index.val + 1) / 64)
    (centerSeparation : ∀ current ∈ Icc 0 terminal, ∀ receiver source : Fin count, receiver ≠ source →
      |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 ≤
        ‖quadrupoleCenter trajectory.movingFamily.patchMotion current receiver -
          quadrupoleCenter trajectory.movingFamily.patchMotion current source‖)
    (boundary : ∀ current ∈ Icc 0 terminal, ∀ index patch,
      BoundaryCloseToCircle scales trajectory.movingFamily.patchMotion current index patch (1 / 16)) :
    ∀ current ∈ Icc 0 terminal, ∀ index,
      ReferenceCentroidFieldGeometry scales trajectory.movingFamily.patchMotion current index := by
  have evolution := trajectory.finitePatchEvolution_of_margin scales densityIdentity radiusIdentity initialCircles
    marginPositive terminalNonnegative beforeFinal safe
  intro current inside index
  exact evolution.reference_centroid_field_geometry inside amplitudePositive frequencyPositive ratioPositive
    (differenceLower current inside) (differenceUpper current inside) (radialSmall current inside)
    (asymmetrySmall current inside) (centerSeparation current inside) lengthSmall radiusSmall
    (fun _ => 1 / 16) (boundary current inside) (by intro; norm_num) (by intro; exact le_rfl) index

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
