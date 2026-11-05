import EulerNonuniqueness.Section4.ReferenceMonitoredContourImprovement
import EulerNonuniqueness.Section4.ReferenceSafePrefixGeometry

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

theorem reference_material_data_of_nonpositive_monitors
    {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
    {shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
    {initial : MovingContourState (count * 4)}
    (trajectory : MovingCentroidGaugeTrajectory configuration 4 shapeRadius gap margin
      backwardHorizon forwardHorizon initial) (scales : Scales)
    (densityIdentity : ∀ index patch, configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (radiusIdentity : ∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1))
    (initialCircles : ∀ label, initial.2.2 label = standardCircleBanach) (initialClock : initial.1 = 0)
    (marginPositive : 0 < margin) {terminal shapeStop : ℝ}
    (terminalNonnegative : 0 ≤ terminal) (beforeFinal : terminal < forwardHorizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (stopSmall : shapeStop ≤ 1 / 48)
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (radiusSmall : ∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000)
    (bounds : ∀ current ∈ Icc 0 terminal, ∀ monitor,
      referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop (trajectory.curve current) monitor ≤ 0) :
    FinitePatchEvolution scales trajectory.movingFamily.patchMotion terminal ∧
    (∀ current ∈ Icc 0 terminal, ∀ index,
      ReferenceCentroidFieldGeometry scales trajectory.movingFamily.patchMotion current index) ∧
    (∀ current ∈ Icc 0 terminal, ∀ index patch,
      BoundaryCloseToCircle scales trajectory.movingFamily.patchMotion current index patch (1 / 16)) ∧
    (∀ current ∈ Icc 0 terminal, ∀ source label,
      (trajectory.movingFamily.patch source).boundaryVelocity current label =
        biotSavart (trajectory.movingFamily.vorticity current) ((trajectory.movingFamily.patch source).boundary current label)) := by
  have inside (current : ℝ) (member : current ∈ Icc 0 terminal) :
      current ∈ Ioo (-backwardHorizon) forwardHorizon :=
    ⟨by linarith [trajectory.backward_positive, member.1], member.2.trans_lt beforeFinal⟩
  have decoded (current : ℝ) (member : current ∈ Icc 0 terminal) :=
    trajectory.reference_paper_geometry_of_nonpositive_monitors scales initialCircles (inside current member) (bounds current member)
  have safe (current : ℝ) (member : current ∈ Icc 0 terminal) := (decoded current member).1
  have evolution := trajectory.finitePatchEvolution_of_margin scales densityIdentity radiusIdentity initialCircles
    marginPositive terminalNonnegative beforeFinal safe
  have boundary (current : ℝ) (member : current ∈ Icc 0 terminal) (index : Fin count) (patch : Fin 4) :
      BoundaryCloseToCircle scales trajectory.movingFamily.patchMotion current index patch (1 / 16) := by
    apply trajectory.movingFamily.boundaryCloseToCircle_of_shape_norm scales current index patch (radiusIdentity index patch)
    · rw [trajectory.movingFamily.patchCentroid_eq]
      exact (trajectory.movingPatch_centroid_eq_center_of_initial_circles initialCircles (inside current member) _).symm
    · exact (trajectory.movingPatch_phase_eq_density_time_of_margin initialClock marginPositive member safe _).trans
        (by rw [densityIdentity])
    · have shapeBound := (referenceMechanicalMonitor_shape (finProdFinEquiv (index, patch))
        (bounds current member (.shape (finProdFinEquiv (index, patch))))).trans stopSmall
      change 3 * ‖(trajectory.curve current).2.2 (finProdFinEquiv (index, patch)) - standardCircleBanach‖ ≤ 1 / 16
      linarith
  refine ⟨evolution, ?_, boundary, ?_⟩
  · intro current member index
    exact evolution.reference_centroid_field_geometry member amplitudePositive frequencyPositive ratioPositive
      (fun other => ((decoded current member).2.1 other).1)
      (fun other => ((decoded current member).2.1 other).2.1)
      (fun other => ((decoded current member).2.1 other).2.2.2.1)
      (fun other => ((decoded current member).2.1 other).2.2.1)
      (fun receiver source different => ((decoded current member).2.2 receiver source different).1)
      lengthSmall radiusSmall (fun _ => 1 / 16) (boundary current member) (by intro; norm_num) (by intro; exact le_rfl) index
  · intro current member source label
    exact trajectory.movingFamily_material_equation_of_margin marginPositive (inside current member) (safe current member) source label

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
