import EulerNonuniqueness.Section4.PaperReferenceCenterVelocity
import EulerNonuniqueness.Section4.ReferenceCoarseMomentAbsorption
import EulerNonuniqueness.Section4.PaperReferenceForeignStrainGeometry

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000

theorem FinitePatchEvolution.norm_reference_external_strainDerivative_le_absorbed
    {count : ℕ} {scales : Scales} {motion : PatchMotion count}
    {horizon time deformation bound : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 192 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) (index : Fin count)
    (control : ∀ patch, BoundaryCloseToCircle scales motion time index patch deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16)
    (boundNonnegative : 0 ≤ bound)
    (deformationBound : deformation ≤ bound / scales.omega (index.val + 1) ^ 2)
    (hessianBound : scales.hessian ≤ 1) (strainBound : scales.strain ≤ 1)
    (momentBound : ‖centroidAsymmetry motion time index‖ ≤ scales.length (index.val + 1) ^ 2)
    (radiusSmall : scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000)
    (transportSmall : scales.omega (index.val + 1) * scales.length (index.val + 1) ≤ scales.location (index.val + 1))
    (lengthSmall : scales.omega (index.val + 1) ^ 4 * scales.length (index.val + 1) ≤ 1)
    (residualSmall : ((13824000000 + 113246208 / Real.pi) * bound / scales.amplitude) ≤
      scales.omega (index.val + 1))
    (geometry : ReferenceCentroidFieldGeometry scales motion time index) :
    ‖externalQuadrupoleStrainDerivative scales motion index time‖ ≤
      (1 + (55296 / Real.pi) * (40001 + 497664 / Real.pi) + 34504704 / Real.pi ^ 2) *
        (scales.strain ^ 2 + (scales.omega (index.val + 1))⁻¹ ^ 4) := by
  have baseFrequency : 1 ≤ scales.frequency := by linarith only [frequencyBound]
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le baseFrequency
  have ratioPositive : 0 < scales.ratio := by linarith only [ratioBound]
  have omegaBound : 1 ≤ scales.omega (index.val + 1) :=
    baseFrequency.trans (scales.omega_ge_frequency frequencyPositive (by linarith only [ratioBound]) _)
  have omegaLarge : 192 ≤ scales.omega (index.val + 1) :=
    frequencyBound.trans (scales.omega_ge_frequency frequencyPositive (by linarith only [ratioBound]) _)
  have lengthPositive := scales.length_pos (index.val + 1)
  have locationPositive := scales.location_pos (index.val + 1)
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have velocityBound := evolution.reference_refined_center_average_velocity_bound inside amplitudePositive baseFrequency
    ratioBound alphaPositive index control nonnegative small boundNonnegative deformationBound
    (scales.length_le_one frequencyPositive ratioPositive _) hessianBound geometry
  have relativeBound := (div_le_div_of_nonneg_right velocityBound locationPositive.le).trans
    (reference_center_defect_absorbed_scale_bound omegaBound lengthPositive locationPositive hessianBound
      residualSmall momentBound transportSmall lengthSmall)
  have receiverBounded := evolution.reference_receiver_domain_bound inside index
    (scales.radius_pos amplitudePositive frequencyPositive ratioPositive _) radiusSmall control small geometry
  have receiverSmall : 2 * (4 * scales.length (index.val + 1)) ≤ scales.location (index.val + 1) / 24 := by
    have multiplied := mul_le_mul_of_nonneg_right omegaLarge lengthPositive.le
    linarith only [multiplied, transportSmall]
  have temporal := evolution.norm_externalQuadrupoleStrainDerivative_le inside amplitudePositive baseFrequency
    ratioBound alphaPositive index receiverBounded receiverSmall geometry.centerSeparated
  let first : ℝ := 55296 / Real.pi
  let centerConstant : ℝ := 40001 + 497664 / Real.pi
  let second : ℝ := 34504704 / Real.pi ^ 2
  have firstNonnegative : 0 ≤ first := by dsimp only [first]; positivity
  have centerNonnegative : 0 ≤ centerConstant := by dsimp only [centerConstant]; positivity
  have secondNonnegative : 0 ≤ second := by dsimp only [second]; positivity
  have inverseNonnegative : 0 ≤ (scales.omega (index.val + 1))⁻¹ ^ 4 := by positivity
  have firstEstimate := mul_le_mul_of_nonneg_left relativeBound (mul_nonneg firstNonnegative strainNonnegative)
  have strainEstimate := mul_le_mul_of_nonneg_right strainBound
    (mul_nonneg (mul_nonneg firstNonnegative centerNonnegative) inverseNonnegative)
  have combined : ‖externalQuadrupoleStrainDerivative scales motion index time‖ ≤
      first * centerConstant * (scales.omega (index.val + 1))⁻¹ ^ 4 + second * scales.strain ^ 2 := by
    have firstRewrite : first * scales.strain * ((40001 + 497664 / Real.pi) / scales.omega (index.val + 1) ^ 4) =
        scales.strain * (first * centerConstant * (scales.omega (index.val + 1))⁻¹ ^ 4) := by
      dsimp only [centerConstant]
      rw [div_eq_mul_inv, inv_pow]
      ring
    rw [firstRewrite] at firstEstimate
    have normalized := firstEstimate.trans (by simpa only [one_mul] using strainEstimate)
    apply temporal.trans
    convert (add_le_add_right normalized (second * scales.strain ^ 2)) using 1 <;>
      dsimp only [first, centerConstant, second] <;> ring
  have firstLarger : first * centerConstant ≤ 1 + first * centerConstant + second := by linarith only [secondNonnegative]
  have secondLarger : second ≤ 1 + first * centerConstant + second := by
    linarith only [mul_nonneg firstNonnegative centerNonnegative]
  have final := add_le_add (mul_le_mul_of_nonneg_right firstLarger inverseNonnegative)
    (mul_le_mul_of_nonneg_right secondLarger (sq_nonneg scales.strain))
  exact combined.trans (final.trans_eq (by dsimp only [first, centerConstant, second]; ring))

end EulerNonuniqueness.Paper
