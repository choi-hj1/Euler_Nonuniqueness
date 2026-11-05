import EulerNonuniqueness.Section6.PaperPatchResidualArrayBound
import EulerNonuniqueness.Section5.CascadeMaterialPreparedPair
import EulerNonuniqueness.Section4.UniversalReferenceMechanicalData
import EulerNonuniqueness.Section1.ForeignInteractionWeight

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem exists_uniform_cascade_reference_patch_error_bound :
    ∃ constant ≥ (1 : ℝ), ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ {threshold referenceConstant : ℝ}, threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ phase dipoleAngle : ℕ → ℝ, ∀ {scaleRoot shapeRadius factor monitor boundaryConstant : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ time ∈ Icc (0 : ℝ) 2, ∀ index : Fin count,
      let changed : Scales := {scales with frequency := frequency}
      ‖quadrupoleDilationPatchError changed prepared.reference index time‖ / changed.length (index.val + 1) ≤
        constant * changed.omega (index.val + 1) *
          (changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2) := by
  let firstConstant : ℝ := 6912 * 100 ^ 3
  let secondConstant : ℝ := 4096 * 13824 / Real.pi
  let constant := 1 + firstConstant + secondConstant
  have firstNonnegative : 0 ≤ firstConstant := by dsimp only [firstConstant]; positivity
  have secondNonnegative : 0 ≤ secondConstant := by dsimp only [secondConstant]; positivity
  have constantOne : 1 ≤ constant := by dsimp only [constant]; linarith
  refine ⟨constant, constantOne, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive threshold referenceConstant thresholdSmall referenceNonnegative
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative,
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency frequencyBound mechanical hessianSmall
  intro count orbit sectionTime phase dipoleAngle scaleRoot shapeRadius factor monitor boundaryConstant prepared time inside index
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let length := changed.length (index.val + 1)
  let omega := changed.omega (index.val + 1)
  let radius := changed.radius (index.val + 1)
  let rho := referenceConstant * (changed.omega (index.val + 1))⁻¹ ^ 2
  let epsilon := radius ^ 2 / length ^ 2
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have lengthPositive : 0 < length := changed.length_pos _
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have omegaOne : 1 ≤ omega := frequencyBound.trans
    (changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith) _)
  have lengthSmall : length ≤ 1 := changed.length_le_one frequencyPositive ratioPositive _
  have epsilonNonnegative : 0 ≤ epsilon := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg (fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (changed.location_pos _).le _))
  obtain ⟨geometry, _, _, _, _, _, _, rhoNonnegative, rhoSmall, boundary⟩ :=
    mechanical motion prepared.referenceWitness.evolution prepared.referenceWitness.coarse time inside index
  have rhoUnit : rho ≤ 1 := rhoSmall.trans (by norm_num)
  have actual := prepared.referenceWitness.evolution.quadrupole_patch_residual_array_bound inside
    amplitudePositive frequencyPositive ratioPositive index (referenceSourceDistance changed index) boundary rhoNonnegative rhoSmall
    (show 0 < length / 100 by positivity) geometry.internalRadius geometry.internalSeparated geometry.positive
    geometry.sourceBounded geometry.receiverSmall geometry.sourceSmall geometry.centroidsSeparated
  have foreign := changed.sum_foreignInteractionWeight_le frequencyBound ratioBound alphaPositive index 3
  have foreign' : (∑ source ∈ Finset.univ.erase index,
      changed.circulation (source.val + 1) / referenceSourceDistance changed index source ^ 3) ≤ 13824 * changed.hessian := by
    convert foreign using 1 <;> norm_num [referenceSourceDistance, Scales.hessian]
  have enlarged := actual.trans (add_le_add_left (mul_le_mul_of_nonneg_left foreign'
    (show 0 ≤ 4096 * radius ^ 2 * rho / Real.pi by positivity)) _)
  have divided := div_le_div_of_nonneg_right enlarged lengthPositive.le
  have identity : (3456 * changed.circulation (index.val + 1) * radius ^ 2 * rho /
      (Real.pi * (length / 100) ^ 3) + (4096 * radius ^ 2 * rho / Real.pi) * (13824 * changed.hessian)) / length =
      firstConstant * (omega * epsilon) * rho + secondConstant * epsilon * (length * rho * changed.hessian) := by
    dsimp only [firstConstant, secondConstant, omega, epsilon, length, Scales.circulation]
    field_simp [(changed.length_pos (index.val + 1)).ne', Real.pi_pos.ne']
    <;> ring
  change ‖quadrupoleDilationPatchError changed motion index time‖ / length ≤ _ at divided
  rw [identity] at divided
  have product : length * rho ≤ 1 := by
    have bound := mul_le_mul lengthSmall rhoUnit rhoNonnegative (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using bound
  have productOmega : length * rho * changed.hessian ≤ omega := by
    have actual := mul_le_mul_of_nonneg_right product hessianNonnegative
    exact actual.trans (by simpa only [one_mul] using hessianSmall.le.trans omegaOne)
  have firstTerm := mul_le_mul_of_nonneg_left rhoUnit (show 0 ≤ firstConstant * (omega * epsilon) by positivity)
  have secondTerm := mul_le_mul_of_nonneg_left productOmega (mul_nonneg secondNonnegative epsilonNonnegative)
  have final := divided.trans (add_le_add firstTerm secondTerm)
  have omegaEpsilon : 0 ≤ omega * epsilon := mul_nonneg omegaPositive.le epsilonNonnegative
  have scalar : firstConstant * (omega * epsilon) * 1 + secondConstant * epsilon * omega ≤ constant * omega * epsilon := by
    dsimp only [constant]
    nlinarith
  have final' := final.trans scalar
  simpa only [motion, prepared.referenceIdentity, omega, epsilon, radius, length] using final'

end EulerNonuniqueness.Paper
