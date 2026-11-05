import EulerNonuniqueness.Section3.MovingCentroidGaugeInitialData
import EulerNonuniqueness.Section3.MovingCentroidGaugeConservation
import EulerNonuniqueness.Section3.MovingContourCutoffMargin
import EulerNonuniqueness.Section3.FiniteMovingPatchEuler

noncomputable section

open Set Metric MeasureTheory

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option synthInstance.maxHeartbeats 100000

variable {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
  {initial : MovingContourState (count * 4)}

theorem finitePatchEvolution_of_margin
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (scales : Scales)
    (densityIdentity : ∀ (index : Fin count) (patch : Fin 4), configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (radiusIdentity : ∀ (index : Fin count) (patch : Fin 4), configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1))
    (initialCircles : ∀ index, initial.2.2 index = standardCircleBanach) (marginPositive : 0 < margin)
    {horizon : ℝ} (nonnegative : 0 ≤ horizon) (beforeFinal : horizon < forwardHorizon)
    (safe : ∀ time ∈ Icc 0 horizon, margin ≤ infDist (trajectory.curve time)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) :
    FinitePatchEvolution scales trajectory.movingFamily.patchMotion horizon := by
  apply trajectory.movingFamily.finitePatchEvolution_of_initialCircles scales densityIdentity radiusIdentity nonnegative
    (fun _ => neg_neg_of_pos trajectory.backward_positive) (fun _ => beforeFinal)
    (fun index => (trajectory.movingPatch_shape_initial index).trans (initialCircles index))
  intro time inside index label
  exact trajectory.movingFamily_material_equation_of_margin marginPositive
    ⟨(neg_neg_of_pos trajectory.backward_positive).trans_le inside.1, inside.2.trans_lt beforeFinal⟩ (safe time inside) index label

theorem isEulerSolutionOn_of_margin
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (scales : Scales)
    (densityIdentity : ∀ (index : Fin count) (patch : Fin 4), configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (radiusIdentity : ∀ (index : Fin count) (patch : Fin 4), configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1))
    (initialCircles : ∀ index, initial.2.2 index = standardCircleBanach) (marginPositive : 0 < margin)
    {horizon : ℝ} (positive : 0 < horizon) (beforeFinal : horizon < forwardHorizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    (safe : ∀ time ∈ Icc 0 horizon, margin ≤ infDist (trajectory.curve time)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) :
    IsEulerSolutionOn horizon (trajectory.movingFamily.vorticity 0) trajectory.movingFamily.vorticity := by
  apply trajectory.movingFamily.isEulerSolutionOn_of_material_equation scales densityIdentity radiusIdentity positive
    amplitudePositive frequencyPositive ratioPositive (fun _ => neg_neg_of_pos trajectory.backward_positive) (fun _ => beforeFinal)
    (fun index => trajectory.movingPatch_area_initial_circle initialCircles index)
  intro time inside index label
  exact trajectory.movingFamily_material_equation_of_margin marginPositive
    ⟨(neg_neg_of_pos trajectory.backward_positive).trans_le inside.1, inside.2.trans_lt beforeFinal⟩ (safe time inside) index label

theorem finitePatchEvolution_of_inner_geometry
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (scales : Scales)
    (densityIdentity : ∀ (index : Fin count) (patch : Fin 4), configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (radiusIdentity : ∀ (index : Fin count) (patch : Fin 4), configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1))
    (initialCircles : ∀ index, initial.2.2 index = standardCircleBanach)
    (countPositive : 0 < count * 4) (centerNonnegative : 0 ≤ centerBound) (marginPositive : 0 < margin)
    {horizon : ℝ} (nonnegative : 0 ≤ horizon) (beforeFinal : horizon < forwardHorizon)
    (centersInside : ∀ time ∈ Icc 0 horizon, ∀ index, ‖(trajectory.curve time).2.1 index‖ + margin ≤ centerBound)
    (shapesInside : ∀ time ∈ Icc 0 horizon, ∀ index, ‖(trajectory.curve time).2.2 index - standardCircleBanach‖ + margin ≤ shapeRadius)
    (separated : ∀ time ∈ Icc 0 horizon, ∀ first second, first ≠ second →
      3 * (configuration.radius first + configuration.radius second) + gap + 2 * margin ≤
        ‖(trajectory.curve time).2.1 first - (trajectory.curve time).2.1 second‖) :
    FinitePatchEvolution scales trajectory.movingFamily.patchMotion horizon := by
  apply trajectory.finitePatchEvolution_of_margin scales densityIdentity radiusIdentity initialCircles marginPositive nonnegative beforeFinal
  intro time inside
  exact configuration.movingStateAdmissible_infDist_lower_bound countPositive centerNonnegative
    (trajectory.curve time) (centersInside time inside) (shapesInside time inside) (separated time inside)

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
