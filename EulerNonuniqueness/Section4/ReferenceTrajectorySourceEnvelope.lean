import EulerNonuniqueness.Section4.ReferenceLocalSourceEnvelope
import EulerNonuniqueness.Section3.MovingCentroidGaugeEuler

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

open EulerNonuniqueness.Section6

theorem reference_eventually_source_envelopes
    {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
    {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
    {initial : MovingContourState (count * 4)}
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial)
    (scales : Scales)
    (densityIdentity : ∀ (index : Fin count) (patch : Fin 4), configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (radiusIdentity : ∀ (index : Fin count) (patch : Fin 4), configuration.radius (finProdFinEquiv (index, patch)) =
      scales.radius (index.val + 1))
    (initialCircles : ∀ index, initial.2.2 index = standardCircleBanach)
    (marginPositive : 0 < margin) {horizon time : ℝ}
    (horizonNonnegative : 0 ≤ horizon) (beforeFinal : horizon < forwardHorizon)
    (safe : ∀ current ∈ Icc 0 horizon, margin ≤ infDist (trajectory.curve current)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ)
    (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyLarge : 1 ≤ scales.frequency)
    (ratioLarge : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (index : Fin count)
    (geometry : ReferenceCentroidFieldGeometry scales trajectory.movingFamily.patchMotion time index)
    (receiver : Fin 4) :
    ∀ᶠ current in 𝓝 time,
      (∀ source ∈ Finset.univ.erase (finProdFinEquiv (index, receiver)),
        scales.length (index.val + 1) / 400 + 3 * (trajectory.movingFamily.patch source).radius ≤
          ‖(trajectory.movingFamily.patch (finProdFinEquiv (index, receiver))).center current -
            (trajectory.movingFamily.patch source).center current‖) ∧
      (∫ position, inverseSquareVorticityWeight
        (trajectory.movingFamily.subfamilyVorticity (Finset.univ.erase (finProdFinEquiv (index, receiver))) current)
        ((trajectory.movingFamily.patch (finProdFinEquiv (index, receiver))).center current) position) ≤
          scales.referenceLocalExteriorWeight (index.val + 1) ∧
      (∫ position, |trajectory.movingFamily.patchVorticity current (finProdFinEquiv (index, receiver)) position|) ≤
        2 * scales.circulation (index.val + 1) := by
  have evolution := trajectory.finitePatchEvolution_of_margin scales densityIdentity radiusIdentity
    initialCircles marginPositive horizonNonnegative beforeFinal safe
  have globalInside : time ∈ Ioo (-backwardHorizon) forwardHorizon :=
    ⟨by linarith [trajectory.backward_positive, inside.1], inside.2.trans_lt beforeFinal⟩
  apply trajectory.movingFamily.reference_eventually_local_source_envelopes scales evolution inside
    densityIdentity radiusIdentity
  · intro source patch
    rw [trajectory.movingFamily.patchCentroid_eq]
    exact (trajectory.movingPatch_centroid_eq_center_of_initial_circles initialCircles globalInside
      (finProdFinEquiv (source, patch))).symm
  · exact amplitudePositive
  · exact frequencyLarge
  · exact ratioLarge
  · exact alphaPositive
  · exact geometry

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
