import EulerNonuniqueness.Section4.PaperReferenceGivenPhase
import EulerNonuniqueness.Section4.ReferencePhaseKinematics
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.reference_dilation_kinematics_of_boundary_gaps
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
    (index : Fin count) :
    ContinuousOn (referenceDilation scales motion index) (Icc 0 horizon) ∧
      ∀ time ∈ Ioo 0 horizon,
        HasDerivAt (referenceDilation scales motion index)
          (deriv (referenceDilation scales motion index) time) time ∧
        referencePositiveDiagonalVelocity scales motion time index =
          deriv (fun current => positiveHalfDiagonal motion current index) time := by
  have data (patch : Fin 4) := evolution.patchCentroid_closed_derivative_of_boundary_gaps
    horizonPositive amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index patch
  have positive : ContinuousOn (fun time => positiveHalfDiagonal motion time index) (Icc 0 horizon) :=
    ((data 0).1.sub (data 1).1).div_const 2
  have negative : ContinuousOn (fun time => negativeHalfDiagonal motion time index) (Icc 0 horizon) :=
    ((data 2).1.sub (data 3).1).div_const 2
  refine ⟨((positive.norm.pow 2).sub (negative.norm.pow 2)).div_const _, ?_⟩
  intro time inside
  have derivative (patch : Fin 4) := ((data patch).2.2 time ⟨inside.1.le, inside.2.le⟩).hasDerivAt
    (Icc_mem_nhds inside.1 inside.2)
  have positiveDerivative := ((derivative 0).sub (derivative 1)).div_const 2
  have negativeDerivative := ((derivative 2).sub (derivative 3)).div_const 2
  constructor
  · exact ((positiveDerivative.norm_sq.sub negativeDerivative.norm_sq).div_const
      (scales.length (index.val + 1) ^ 2)).differentiableAt.hasDerivAt
  · exact positiveDerivative.deriv.symm

end EulerNonuniqueness.Paper
