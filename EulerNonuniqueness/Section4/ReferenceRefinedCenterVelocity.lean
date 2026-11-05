import EulerNonuniqueness.Section4.ReferenceRefinedCenterDynamics
import EulerNonuniqueness.Section4.ReferenceCentroidFieldGeometry
import EulerNonuniqueness.Section4.ReferenceCenterDeformationScale
import EulerNonuniqueness.Section4.ReferenceNeutralForcingScale

noncomputable section

open Set EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 1000000

theorem reference_refined_center_velocity_bound {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    {horizon time deformation bound : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) (index : Fin count)
    (pathInside : ∀ patch : Fin 4, time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ patch label, (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
      biotSavart (Paper.patchVorticity scales family.patchMotion time)
        ((family.patch (finProdFinEquiv (index, patch))).boundary time label))
    (control : ∀ patch, BoundaryCloseToCircle scales family.patchMotion time index patch deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16)
    (boundNonnegative : 0 ≤ bound)
    (deformationBound : deformation ≤ bound / scales.omega (index.val + 1) ^ 2)
    (lengthBound : scales.length (index.val + 1) ≤ 1) (hessianBound : scales.hessian ≤ 1)
    (geometry : ReferenceCentroidFieldGeometry scales family.patchMotion time index) :
    ‖deriv (fun current => quadrupoleCenter family.patchMotion current index) time -
        biotSavart (externalPatchVorticity scales family.patchMotion time index)
          (quadrupoleCenter family.patchMotion time index)‖ ≤
      40000 * scales.omega (index.val + 1) * ‖centroidAsymmetry family.patchMotion time index‖ +
        (497664 / Real.pi) * scales.hessian * scales.length (index.val + 1) ^ 2 +
        ((13824000000 + 113246208 / Real.pi) * bound / scales.amplitude) *
          (scales.length (index.val + 1) / scales.omega (index.val + 1) ^ 4) := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have lengthPositive := scales.length_pos (index.val + 1)
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have estimate := family.quadrupoleCenter_refined_relative_deriv_bound scales evolution inside amplitudePositive
    frequencyPositive ratioPositive index pathInside material control nonnegative small (by positivity)
    geometry.internalRadius geometry.internalSeparated (referenceSourceDistance scales index) geometry.positive
    geometry.sourceBounded geometry.receiverSmall geometry.sourceSmall geometry.centroidsSeparated (by positivity)
    geometry.centroidsBounded geometry.centerSeparated geometry.near
  have internalIdentity :
      |scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2| *
          ‖fourPointSignedMoment (fun patch => patchCentroid family.patchMotion time index patch)‖ /
          (scales.length (index.val + 1) / 100) ^ 2 =
        40000 * scales.omega (index.val + 1) * ‖centroidAsymmetry family.patchMotion time index‖ := by
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

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
