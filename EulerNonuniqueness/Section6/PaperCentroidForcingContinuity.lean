import EulerNonuniqueness.Section6.PaperCentroidEndpoints
import EulerNonuniqueness.Section6.MovingMaterialShapeDynamics

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.quadrupoleCentroidForcing_continuousOn_of_boundary_gaps
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (horizonPositive : 0 < horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (radiusPositive : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
    (control : ∀ current ∈ Icc 0 horizon, ∀ index patch,
      ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle scales motion current index patch bound)
    (separated : ∀ current ∈ Icc 0 horizon, ∀ (index other : Fin count) (patch otherPatch : Fin 4),
      (other, otherPatch) ≠ (index, patch) →
      8 * scales.radius (index.val + 1) + 8 * scales.radius (other.val + 1) <
        dist (motion.boundary current index patch 0) (motion.boundary current other otherPatch 0))
    (index : Fin count)
    (noncollision : ∀ time ∈ Icc 0 horizon,
      Section6.FourPointNoncollision (fun patch => patchCentroid motion time index patch))
    (patch : Fin 4) :
    ContinuousOn (fun time => quadrupoleCentroidForcing scales motion time index patch) (Icc 0 horizon) := by
  have centroidData (source : Fin 4) := evolution.patchCentroid_closed_derivative_of_boundary_gaps
    horizonPositive amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index source
  have configuration : ContinuousOn (fun time source => patchCentroid motion time index source) (Icc 0 horizon) :=
    continuousOn_pi.mpr fun source => (centroidData source).1
  have field : ContinuousOn (fun time => Section6.fourPointField
      (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
      (fun source => patchCentroid motion time index source) patch) (Icc 0 horizon) := by
    intro time inside
    have regularity := Section6.fourPointField_contDiffAt
      (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2) (noncollision time inside)
    have fieldContinuous : ContinuousWithinAt (fun current => Section6.fourPointField
        (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
        (fun source => patchCentroid motion current index source)) (Icc 0 horizon) time :=
      ContinuousAt.comp_continuousWithinAt
        (f := fun current source => patchCentroid motion current index source)
        regularity.continuousAt (configuration time inside)
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun current => Section6.fourPointField
        (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
        (fun source => patchCentroid motion current index source))
      (continuous_apply patch).continuousAt fieldContinuous
  apply ((centroidData patch).2.1.sub field).congr
  intro time inside
  have decomposition := evolution.patch_average_velocity_decomposition inside index patch
  dsimp only [quadrupoleCentroidForcing]
  rw [decomposition]
  abel

end EulerNonuniqueness.Paper
