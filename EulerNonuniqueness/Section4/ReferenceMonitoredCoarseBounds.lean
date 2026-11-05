import EulerNonuniqueness.Section4.ReferenceMonitoredMaterialPrefix
import EulerNonuniqueness.Section4.ReferenceNeutralMoment
import EulerNonuniqueness.Section3.MovingCentroidGaugeDisjointness

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

def referenceCoarseBoundConstant (bound : ℝ) : ℝ := 1 + bound + 497664 / Real.pi + 1152 / Real.pi

theorem referenceCoarseBoundConstant_bounds {bound : ℝ} (nonnegative : 0 ≤ bound) :
    0 < referenceCoarseBoundConstant bound ∧ bound ≤ referenceCoarseBoundConstant bound ∧
      497664 / Real.pi ≤ referenceCoarseBoundConstant bound ∧ 1152 / Real.pi ≤ referenceCoarseBoundConstant bound := by
  have firstPositive : (0 : ℝ) < 497664 / Real.pi := by positivity
  have secondPositive : (0 : ℝ) < 1152 / Real.pi := by positivity
  dsimp only [referenceCoarseBoundConstant]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

namespace MovingCentroidGaugeTrajectory

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

theorem referenceCoarseBounds_of_monitors_and_shape_confinement
    {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
    {shapeRadius gap margin : ℝ} {initial : MovingContourState (count * 4)}
    (trajectory : MovingCentroidGaugeTrajectory configuration 4 shapeRadius gap margin 1 3 initial)
    (scales : Scales)
    (densityIdentity : ∀ index patch, configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (radiusIdentity : ∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1))
    (initialCircles : ∀ label, initial.2.2 label = standardCircleBanach) (initialClock : initial.1 = 0)
    (marginPositive : 0 < margin) (amplitudePositive : 0 < scales.amplitude)
    (frequencyLarge : 1 ≤ scales.frequency) (ratioLarge : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {shapeStop threshold initialThreshold bound : ℝ} (stopSmall : shapeStop ≤ 1 / 48) (boundNonnegative : 0 ≤ bound)
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (radiusSmall : ∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000)
    {phase unstable : Fin count → ℝ}
    (initialDisks : ReferenceInitialDisks scales trajectory.movingFamily.patchMotion phase unstable initialThreshold)
    (bounds : ∀ current ∈ Icc (0 : ℝ) 2, ∀ monitor,
      referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop (trajectory.curve current) monitor ≤ 0)
    (shapeBounds : ∀ current ∈ Icc (0 : ℝ) 2, ∀ index,
      |unstableShape trajectory.movingFamily.patchMotion current index| ≤ threshold ∧
      |stableShape trajectory.movingFamily.patchMotion current index| ≤ threshold)
    (boundary : ∀ current ∈ Icc (0 : ℝ) 2, ∀ index patch,
      BoundaryCloseToCircle scales trajectory.movingFamily.patchMotion current index patch (bound / scales.omega (index.val + 1) ^ 2)) :
    ReferenceCoarseBounds scales trajectory.movingFamily.patchMotion threshold (referenceCoarseBoundConstant bound) := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyLarge
  have ratioPositive : 0 < scales.ratio := by linarith
  obtain ⟨evolution, _, coarseBoundary, material⟩ := trajectory.reference_material_data_of_nonpositive_monitors scales
    densityIdentity radiusIdentity initialCircles initialClock marginPositive (by norm_num) (by norm_num)
    amplitudePositive frequencyPositive ratioPositive stopSmall lengthSmall radiusSmall bounds
  have inside (current : ℝ) (member : current ∈ Icc (0 : ℝ) 2) : current ∈ Ioo (-1 : ℝ) 3 := by
    constructor <;> linarith [member.1, member.2]
  have decoded (current : ℝ) (member : current ∈ Icc (0 : ℝ) 2) :=
    trajectory.reference_paper_geometry_of_nonpositive_monitors scales initialCircles (inside current member) (bounds current member)
  have memory (index : Fin count) := trajectory.movingFamily.reference_centroidAsymmetry_bound scales densityIdentity evolution
    (by norm_num) (by norm_num) (Subset.refl _) amplitudePositive frequencyLarge ratioLarge alphaPositive initialDisks
    (fun current member _ => inside current member) material
    (fun current member other => ((decoded current member).2.1 other).1)
    (fun current member other => ((decoded current member).2.1 other).2.1)
    (fun current member other => ((decoded current member).2.1 other).2.2.2.1)
    (fun current member other => ((decoded current member).2.1 other).2.2.1)
    (fun current member receiver source different => ((decoded current member).2.2 receiver source different).1)
    lengthSmall coarseBoundary (by
      intro other
      have radiusPositive := scales.radius_pos amplitudePositive frequencyPositive ratioPositive (other.val + 1)
      linarith [radiusSmall other, scales.length_pos (other.val + 1)]) index
  have constants := referenceCoarseBoundConstant_bounds boundNonnegative
  have constantNonnegative := constants.1.le
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ scales.hessian := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (scales.location_pos _).le _)
  refine ⟨trajectory.patchesDisjoint_on_interval (by norm_num), ?_, ?_⟩
  · intro current member index
    have diagonal : |diagonalDifference trajectory.movingFamily.patchMotion current index /
        scales.length (index.val + 1) ^ 2 - 1| ≤ 1 / 2 := by
      have estimate := sub_nonpos.mp (bounds current member (.diagonal index))
      change |movingReferenceDiagonalDifference (trajectory.curve current) index / scales.length (index.val + 1) ^ 2 - 1| ≤ 1 / 2 at estimate
      rwa [(trajectory.movingReferenceGeometricObservables_eq_paper initialCircles (inside current member) index).1] at estimate
    have lower : (1 / 2 : ℝ) ≤ diagonalDifference trajectory.movingFamily.patchMotion current index / scales.length (index.val + 1) ^ 2 :=
      by linarith [(abs_le.mp diagonal).1]
    have upper : diagonalDifference trajectory.movingFamily.patchMotion current index / scales.length (index.val + 1) ^ 2 ≤ 2 :=
      by linarith [(abs_le.mp diagonal).2]
    refine ⟨(shapeBounds current member index).1, (shapeBounds current member index).2, lower, upper, ?_, ?_⟩
    · apply (memory index current member).trans
      have timeNonnegative := member.1
      gcongr <;> first | positivity | exact constants.2.2.1 | exact constants.2.2.2
    · intro patch
      obtain ⟨relabeling, periodic, relabelingBound, errorBound⟩ := boundary current member index patch
      refine ⟨relabeling, periodic, relabelingBound, errorBound.mono ?_⟩
      simpa only [div_eq_mul_inv, inv_pow] using
        mul_le_mul_of_nonneg_right constants.2.1 (sq_nonneg (scales.omega (index.val + 1))⁻¹)
  · intro current member receiver source different
    exact (decoded current member).2.2 receiver source different

end MovingCentroidGaugeTrajectory

end EulerNonuniqueness.Paper
