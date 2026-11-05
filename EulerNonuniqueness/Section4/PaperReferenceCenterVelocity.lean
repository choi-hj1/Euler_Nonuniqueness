import EulerNonuniqueness.Section4.PaperRefinedCenterDynamics
import EulerNonuniqueness.Section4.ReferenceCentroidFieldGeometry
import EulerNonuniqueness.Section4.ReferenceCenterDeformationScale
import EulerNonuniqueness.Section4.ReferenceNeutralForcingScale

noncomputable section

open Set EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000

theorem FinitePatchEvolution.reference_refined_center_average_velocity_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count}
    {horizon time deformation bound : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) (index : Fin count)
    (control : ∀ patch, BoundaryCloseToCircle scales motion time index patch deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16)
    (boundNonnegative : 0 ≤ bound)
    (deformationBound : deformation ≤ bound / scales.omega (index.val + 1) ^ 2)
    (lengthBound : scales.length (index.val + 1) ≤ 1) (hessianBound : scales.hessian ≤ 1)
    (geometry : ReferenceCentroidFieldGeometry scales motion time index) :
    ‖((∑ patch : Fin 4, patchAverageVelocity scales motion time index patch
          (biotSavart (patchVorticity scales motion time))) / 4) -
        biotSavart (externalPatchVorticity scales motion time index) (quadrupoleCenter motion time index)‖ ≤
      40000 * scales.omega (index.val + 1) * ‖centroidAsymmetry motion time index‖ +
        (497664 / Real.pi) * scales.hessian * scales.length (index.val + 1) ^ 2 +
        ((13824000000 + 113246208 / Real.pi) * bound / scales.amplitude) *
          (scales.length (index.val + 1) / scales.omega (index.val + 1) ^ 4) := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith only [ratioBound]
  have lengthPositive := scales.length_pos (index.val + 1)
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have estimate := evolution.quadrupoleCenter_refined_average_velocity_bound inside amplitudePositive
    frequencyPositive ratioPositive index control nonnegative small (by positivity)
    geometry.internalRadius geometry.internalSeparated (referenceSourceDistance scales index) geometry.positive
    geometry.sourceBounded geometry.receiverSmall geometry.sourceSmall geometry.centroidsSeparated (by positivity)
    geometry.centroidsBounded geometry.centerSeparated geometry.near
  have internalIdentity :
      |scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2| *
          ‖fourPointSignedMoment (fun patch => patchCentroid motion time index patch)‖ /
          (scales.length (index.val + 1) / 100) ^ 2 =
        40000 * scales.omega (index.val + 1) * ‖centroidAsymmetry motion time index‖ := by
    rw [centroid_fourPointSignedMoment, norm_mul, abs_of_nonneg (by positivity)]
    have normFour : ‖(4 : ℂ)‖ = (4 : ℝ) := by norm_num
    rw [normFour]
    field_simp
    <;> ring
  have hessianEstimate := mul_le_mul_of_nonneg_right
    (scales.foreign_hessian_weight_le frequencyBound ratioBound alphaPositive index)
    (sq_nonneg (3 * scales.length (index.val + 1)))
  have deformationEstimate := scales.reference_center_deformation_cost_le amplitudePositive frequencyBound
    ratioBound alphaPositive index nonnegative boundNonnegative deformationBound lengthBound hessianBound
  rw [internalIdentity] at estimate
  exact estimate.trans ((add_le_add (add_le_add le_rfl hessianEstimate) deformationEstimate).trans_eq (by ring))

end EulerNonuniqueness.Paper
