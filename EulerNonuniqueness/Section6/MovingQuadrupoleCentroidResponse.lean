import EulerNonuniqueness.Section6.MovingQuadrupoleReceiverDecomposition
import EulerNonuniqueness.Section6.MovingMaterialCentroidDynamics
import EulerNonuniqueness.Section5.CascadeMaterialCenterGeometry

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

def FiniteMovingPatchFamily.receivingCentroidResponse {count : ℕ}
    (family : FiniteMovingPatchFamily count) (receiver : Fin count) (time : ℝ) : ℂ :=
  (family.patch receiver).radius • ((Circle.exp ((family.patch receiver).phase time) : ℂ) *
    contourExteriorCentroidResponse (Circle.exp ((family.patch receiver).phase time))
      (fun power => family.exteriorTaylorCoefficient (Finset.univ.erase receiver)
        (family.patch receiver).center (family.patch receiver).radius (power + 1) time)
      ((family.patch receiver).shape time))

def FiniteMovingPatchFamily.ownSourceCentroidCorrection {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (receiver : Fin count × Fin 4) (time : ℝ) : ℂ :=
  ∑ patch ∈ Finset.univ.erase receiver.2,
    (family.patch (finProdFinEquiv (receiver.1, patch))).sourceVelocityCentroidCorrection
      (family.density (finProdFinEquiv (receiver.1, patch)))
      ((family.patch (finProdFinEquiv receiver)).center time) time

namespace MovingCentroidGaugeTrajectory

variable {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
  {initial : MovingContourState (count * 4)}

theorem paperCentroidResidual_eq_source_and_response
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial)
    (initialClock : initial.1 = 0) (initialCircles : ∀ label, initial.2.2 label = standardCircleBanach)
    (marginPositive : 0 < margin) {scales : Scales} {horizon time distance : ℝ}
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (densityIdentity : ∀ index patch, configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (evolution : FinitePatchEvolution scales trajectory.movingFamily.patchMotion horizon)
    (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (nonnegativeTime : time ∈ Icc 0 horizon)
    (safe : ∀ current ∈ Icc 0 horizon, margin ≤ infDist (trajectory.curve current)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ)
    (receiver : Fin count × Fin 4) (positive : 0 < distance)
    (small : 8 * (trajectory.movingFamily.patch (finProdFinEquiv receiver)).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase (finProdFinEquiv receiver),
      ∀ position ∈ (trajectory.movingFamily.patch source).domain time,
        distance ≤ ‖(trajectory.movingFamily.patch (finProdFinEquiv receiver)).center time - position‖)
    (area : contourAreaFunctional ((trajectory.curve time).2.2 (finProdFinEquiv receiver)) = Real.pi)
    (ratio : 24 * (trajectory.movingFamily.patch (finProdFinEquiv receiver)).radius / distance < 1) :
    quadrupoleInternalPatchResidual scales trajectory.movingFamily.patchMotion time receiver.1 receiver.2 +
      quadrupoleExternalReceiverResidual scales trajectory.movingFamily.patchMotion time receiver.1 receiver.2 =
      trajectory.movingFamily.ownSourceCentroidCorrection receiver time +
        trajectory.movingFamily.receivingCentroidResponse (finProdFinEquiv receiver) time := by
  let family := trajectory.movingFamily
  have centers (current : ℝ) (member : current ∈ Ioo (-backwardHorizon) forwardHorizon) (patch : Fin 4) :
      (family.patch (finProdFinEquiv (receiver.1, patch))).center current =
        patchCentroid family.patchMotion current receiver.1 patch :=
    trajectory.cascadeCenters_eq_patchCentroid initialCircles member receiver.1 patch
  have initialCentered (label : Fin (count * 4)) : contourCentroidFunctional (initial.2.2 label) = 0 := by
    rw [initialCircles label, contourCentroidFunctional_standardCircle_zero]
  have response := trajectory.centerVelocity_eq_exterior_value_and_response initialClock initialCentered
    marginPositive inside nonnegativeTime safe (finProdFinEquiv receiver) positive small separated area ratio
  have actualPhase := trajectory.movingPatch_phase_eq_density_time_of_margin initialClock marginPositive
    nonnegativeTime safe (finProdFinEquiv receiver)
  change (family.patch (finProdFinEquiv receiver)).phase time =
    configuration.density (finProdFinEquiv receiver) * time / 2 at actualPhase
  have responseIdentity : configuration.radius (finProdFinEquiv receiver) •
      ((Circle.exp (configuration.density (finProdFinEquiv receiver) * time / 2) : ℂ) *
        contourExteriorCentroidResponse (Circle.exp (configuration.density (finProdFinEquiv receiver) * time / 2))
          (fun power => family.exteriorTaylorCoefficient (Finset.univ.erase (finProdFinEquiv receiver))
            (family.patch (finProdFinEquiv receiver)).center (family.patch (finProdFinEquiv receiver)).radius (power + 1) time)
          ((trajectory.curve time).2.2 (finProdFinEquiv receiver))) =
      family.receivingCentroidResponse (finProdFinEquiv receiver) time := by
    unfold FiniteMovingPatchFamily.receivingCentroidResponse
    rw [actualPhase]
    rfl
  rw [responseIdentity, family.biotSavart_erased_eq_internal_centroids_and_foreign] at response
  have masses (patch : Fin 4) : (family.quadrupoleSubfamily receiver.1).density patch *
      volume.real (((family.quadrupoleSubfamily receiver.1).patch patch).domain time) =
        patchSign patch * scales.circulation (receiver.1.val + 1) := by
    have patchArea : volume.real (((family.quadrupoleSubfamily receiver.1).patch patch).domain time) =
        Real.pi * scales.radius (receiver.1.val + 1) ^ 2 := by
      change (volume (family.patchMotion.domain time receiver.1 patch)).toReal = _
      rw [(evolution.2.2.2.1 time nonnegativeTime receiver.1 patch).2.2.1,
        ENNReal.toReal_ofReal (by positivity)]
    rw [patchArea]
    change configuration.density (finProdFinEquiv (receiver.1, patch)) * _ = _
    rw [densityIdentity, ← scales.patch_circulation amplitudePositive frequencyPositive ratioPositive]
    ring
  have pointIdentity :
      (∑ patch ∈ Finset.univ.erase receiver.2,
        ((family.quadrupoleSubfamily receiver.1).density patch *
          volume.real (((family.quadrupoleSubfamily receiver.1).patch patch).domain time)) •
          biotSavartKernel ((family.patch (finProdFinEquiv receiver)).center time -
            ((family.quadrupoleSubfamily receiver.1).patch patch).center time)) =
      Section6.fourPointField (scales.omega (receiver.1.val + 1) * scales.length (receiver.1.val + 1) ^ 2)
        (fun patch => patchCentroid family.patchMotion time receiver.1 patch) receiver.2 := by
    simp_rw [masses]
    change (∑ patch ∈ Finset.univ.erase receiver.2, (patchSign patch * scales.circulation (receiver.1.val + 1)) •
      biotSavartKernel ((family.patch (finProdFinEquiv receiver)).center time -
        (family.patch (finProdFinEquiv (receiver.1, patch))).center time)) = _
    simp_rw [centers time inside]
    exact quadrupole_internal_point_field scales family.patchMotion time receiver.1 receiver.2
  have foreignDensity (source : Fin count) : (family.quadrupoleSubfamily source).vorticity time =
      quadrupoleDensity scales family.patchMotion time source := by
    funext position
    apply Finset.sum_congr rfl
    intro patch _
    change ((family.patch (finProdFinEquiv (source, patch))).domain time).indicator
      (fun _ => configuration.density (finProdFinEquiv (source, patch))) position = _
    rw [densityIdentity]
    rfl
  have foreignIdentity : (∑ source ∈ Finset.univ.erase receiver.1,
      biotSavart ((family.quadrupoleSubfamily source).vorticity time)
        ((family.patch (finProdFinEquiv receiver)).center time)) =
      biotSavart (externalPatchVorticity scales family.patchMotion time receiver.1)
        (patchCentroid family.patchMotion time receiver.1 receiver.2) := by
    simp_rw [foreignDensity, centers time inside receiver.2]
    rw [evolution.externalPatch_biotSavart_eq_sum nonnegativeTime]
    exact Finset.sum_congr rfl fun source _ =>
      evolution.quadrupole_biotSavart_eq_sum_patch nonnegativeTime source _
  rw [pointIdentity, foreignIdentity] at response
  have mechanical : HasDerivAt (fun current => patchCentroid family.patchMotion current receiver.1 receiver.2)
      ((trajectory.velocity time).2.1 (finProdFinEquiv receiver)) time := by
    apply (trajectory.center_hasDerivAt (finProdFinEquiv receiver) time).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds inside] with current member
    exact (centers current member receiver.2).symm
  have paper := family.patchCentroid_hasDerivAt_point_field evolution nonnegativeTime receiver.1 receiver.2 inside
    (by
      intro angle
      rw [family.patchVorticity_eq scales densityIdentity]
      exact trajectory.movingFamily_material_equation_of_margin marginPositive inside
        (safe time nonnegativeTime) (finProdFinEquiv receiver) angle)
  have equality := mechanical.unique paper
  change (trajectory.velocity time).2.1 (finProdFinEquiv receiver) = _ at equality
  change (trajectory.velocity time).2.1 (finProdFinEquiv receiver) =
    _ + family.ownSourceCentroidCorrection receiver time + _ + _ at response
  rw [response] at equality
  change _ = family.ownSourceCentroidCorrection receiver time + family.receivingCentroidResponse (finProdFinEquiv receiver) time
  linear_combination -equality

end MovingCentroidGaugeTrajectory

end EulerNonuniqueness.Paper
