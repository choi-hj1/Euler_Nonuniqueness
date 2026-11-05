import EulerNonuniqueness.Section6.PaperPatchResidualArrayBound
import EulerNonuniqueness.Section5.CascadeStoppedMaterialGeometry
import EulerNonuniqueness.Section5.CascadeGeometricScaleSmallness
import EulerNonuniqueness.Section1.ForeignInteractionWeight

noncomputable section

open Set Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem exists_uniform_cascade_stopped_patch_error_bound {factor : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∃ constant ≥ (1 : ℝ), ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ {scaleRoot boundaryConstant : ℝ}, 0 < scaleRoot → 0 ≤ boundaryConstant →
      ∀ᶠ frequency : ℝ in atTop,
      ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
        {threshold referenceConstant shapeRadius monitor : ℝ} {count : ℕ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ time ∈ Icc 0 path.stop, ∀ index : Fin count,
      let changed : Scales := {scales with frequency := frequency}
      ‖quadrupoleDilationPatchError changed prepared.trajectory.movingFamily.patchMotion index time‖ /
          changed.length (index.val + 1) ≤
        constant * changed.omega (index.val + 1) *
          (changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2) := by
  let firstConstant := 6912 / factor ^ 3
  let secondConstant := 4096 * 13824 / Real.pi
  let constant := 1 + firstConstant + secondConstant
  have firstNonnegative : 0 ≤ firstConstant := by dsimp only [firstConstant]; positivity
  have secondNonnegative : 0 ≤ secondConstant := by dsimp only [secondConstant]; positivity
  refine ⟨constant, by dsimp only [constant]; linarith, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant rootPositive boundaryNonnegative
  have boundaryLimit : Tendsto (fun frequency : ℝ => (boundaryConstant / scaleRoot ^ 2) * frequency⁻¹ ^ 2)
      atTop (𝓝 0) := by
    simpa using ((tendsto_inv_atTop_zero : Tendsto (fun frequency : ℝ => frequency⁻¹) atTop (𝓝 0)).pow 2).const_mul
      (boundaryConstant / scaleRoot ^ 2)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := factor) (bound := 3) factorPositive factorSmall (by norm_num),
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num),
    boundaryLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency frequencyBound internalGeometry locationGeometry boundarySmall hessianSmall
  intro orbit sectionTime phase dipoleAngle threshold referenceConstant shapeRadius monitor count prepared path time inside index
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let length := changed.length (index.val + 1)
  let radius := changed.radius (index.val + 1)
  let omega := changed.omega (index.val + 1)
  let rho := boundaryConstant / (scaleRoot ^ 2 * omega ^ 2)
  let distance := fun source : Fin count => |changed.location (index.val + 1) - changed.location (source.val + 1)| / 8
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have lengthPositive : 0 < length := changed.length_pos _
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have omegaOne : 1 ≤ omega := frequencyBound.trans
    (changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith) _)
  have rhoNonnegative : 0 ≤ rho := by dsimp only [rho]; positivity
  have rhoSmall : rho ≤ 1 / 16 := by
    have omegaBound := changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith) (index.val + 1)
    have inverseBound := pow_le_pow_left₀ (inv_nonneg.mpr omegaPositive.le) (inv_anti₀ frequencyPositive omegaBound) 2
    have actual := (mul_le_mul_of_nonneg_left inverseBound
      (show 0 ≤ boundaryConstant / scaleRoot ^ 2 by positivity)).trans boundarySmall.le
    convert actual using 1 <;> dsimp only [rho, omega] <;> field_simp [rootPositive.ne', omegaPositive.ne'] <;> ring
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 := ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have sourceBounded (source : Fin count) (_ : source ∈ Finset.univ.erase index) (patch : Fin 4) :
      motion.domain time source patch ⊆ closedBall (patchCentroid motion time source patch) (2 * changed.radius (source.val + 1)) :=
    prepared.trajectory.domain_subset_centroid_ball changed prepared.radiusIdentity (fun _ => rfl) globalInside source patch
  have positive (source : Fin count) (member : source ∈ Finset.univ.erase index) : 0 < distance source :=
    div_pos (changed.location_distance_pos (fun equality =>
      (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equality).symm))) (by norm_num)
  have locationRadius (source : Fin count) : changed.radius (source.val + 1) ≤ changed.location (source.val + 1) / 1000 :=
    (locationGeometry (source.val + 1)).2.2.2
  have pairLocation (source : Fin count) (member : source ∈ Finset.univ.erase index) :=
    changed.location_sum_le_three_distance (show index.val + 1 ≠ source.val + 1 from
      fun equality => (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equality).symm))
  have receiverSmall (source : Fin count) (member : source ∈ Finset.univ.erase index) : 8 * radius ≤ distance source := by
    have sumBound := pairLocation source member
    have radiusBound := locationRadius index
    change changed.location (index.val + 1) + changed.location (source.val + 1) ≤
      3 * |changed.location (index.val + 1) - changed.location (source.val + 1)| at sumBound
    change radius ≤ changed.location (index.val + 1) / 1000 at radiusBound
    change 8 * radius ≤ |changed.location (index.val + 1) - changed.location (source.val + 1)| / 8
    linarith [changed.location_pos (source.val + 1),
      abs_nonneg (changed.location (index.val + 1) - changed.location (source.val + 1))]
  have sourceSmall (source : Fin count) (member : source ∈ Finset.univ.erase index) :
      4 * changed.radius (source.val + 1) ≤ distance source := by
    have sumBound := pairLocation source member
    have radiusBound := locationRadius source
    change changed.location (index.val + 1) + changed.location (source.val + 1) ≤
      3 * |changed.location (index.val + 1) - changed.location (source.val + 1)| at sumBound
    change 4 * changed.radius (source.val + 1) ≤
      |changed.location (index.val + 1) - changed.location (source.val + 1)| / 8
    linarith [changed.location_pos (index.val + 1),
      abs_nonneg (changed.location (index.val + 1) - changed.location (source.val + 1))]
  have separated (receiver : Fin 4) (source : Fin count) (member : source ∈ Finset.univ.erase index) (patch : Fin 4) :
      distance source ≤ ‖patchCentroid motion time index receiver - patchCentroid motion time source patch‖ := by
    have centers := (path.quadrupole_pair_bounds inside index source (Finset.mem_erase.mp member).1.symm).1
    have firstExtent := path.centroid_extent inside index receiver
    have secondExtent := path.centroid_extent inside source patch
    have locations := pairLocation source member
    change |changed.location (index.val + 1) - changed.location (source.val + 1)| / 2 <
      ‖quadrupoleCenter motion time index - quadrupoleCenter motion time source‖ at centers
    change ‖patchCentroid motion time index receiver - quadrupoleCenter motion time index‖ <
      changed.location (index.val + 1) / 100 at firstExtent
    change ‖patchCentroid motion time source patch - quadrupoleCenter motion time source‖ <
      changed.location (source.val + 1) / 100 at secondExtent
    change changed.location (index.val + 1) + changed.location (source.val + 1) ≤
      3 * |changed.location (index.val + 1) - changed.location (source.val + 1)| at locations
    have firstTriangle := norm_sub_le_norm_sub_add_norm_sub (quadrupoleCenter motion time index)
      (patchCentroid motion time index receiver) (quadrupoleCenter motion time source)
    have secondTriangle := norm_sub_le_norm_sub_add_norm_sub (patchCentroid motion time index receiver)
      (patchCentroid motion time source patch) (quadrupoleCenter motion time source)
    rw [norm_sub_rev (quadrupoleCenter motion time index) (patchCentroid motion time index receiver)] at firstTriangle
    dsimp only [distance]
    linarith [abs_nonneg (changed.location (index.val + 1) - changed.location (source.val + 1))]
  have radiusInternal : 8 * radius ≤ factor * length := by
    have actual := (internalGeometry (index.val + 1)).2.1
    change radius ≤ factor * length / 1000 at actual
    linarith [mul_pos factorPositive lengthPositive]
  have actual := path.evolution.quadrupole_patch_residual_array_bound inside amplitudePositive frequencyPositive ratioPositive index distance
    (path.boundary time inside index) rhoNonnegative rhoSmall (mul_pos factorPositive lengthPositive) radiusInternal
    (fun receiver source different => path.internal_centroid_gap inside index receiver source different.symm)
    positive sourceBounded receiverSmall sourceSmall separated
  have foreign := changed.sum_foreignInteractionWeight_le frequencyBound ratioBound alphaPositive index 3
  have foreign' : (∑ source ∈ Finset.univ.erase index, changed.circulation (source.val + 1) / distance source ^ 3) ≤
      13824 * changed.hessian := by
    convert foreign using 1 <;> norm_num [distance, Scales.hessian]
  have enlarged := actual.trans (add_le_add_left (mul_le_mul_of_nonneg_left foreign'
    (show 0 ≤ 4096 * radius ^ 2 * rho / Real.pi by positivity)) _)
  have divided := div_le_div_of_nonneg_right enlarged lengthPositive.le
  let epsilon := radius ^ 2 / length ^ 2
  have identity : (3456 * changed.circulation (index.val + 1) * radius ^ 2 * rho /
      (Real.pi * (factor * length) ^ 3) + (4096 * radius ^ 2 * rho / Real.pi) * (13824 * changed.hessian)) / length =
      firstConstant * (omega * epsilon) * rho + secondConstant * epsilon * (length * rho * changed.hessian) := by
    dsimp only [firstConstant, secondConstant, omega, epsilon, length, Scales.circulation]
    field_simp [factorPositive.ne', (changed.length_pos (index.val + 1)).ne', Real.pi_pos.ne']
    <;> ring
  change ‖quadrupoleDilationPatchError changed motion index time‖ / length ≤ _ at divided
  rw [identity] at divided
  have rhoOne : rho ≤ 1 := rhoSmall.trans (by norm_num)
  have lengthOne : length ≤ 1 := changed.length_le_one frequencyPositive ratioPositive _
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
  have product : length * rho * changed.hessian ≤ omega := by
    have first := mul_le_mul lengthOne rhoOne rhoNonnegative (by norm_num : (0 : ℝ) ≤ 1)
    have second := mul_le_mul_of_nonneg_right first hessianNonnegative
    exact second.trans (by simpa only [one_mul] using hessianSmall.le.trans omegaOne)
  have firstTerm := mul_le_mul_of_nonneg_left rhoOne (show 0 ≤ firstConstant * (omega * epsilon) by positivity)
  have secondTerm := mul_le_mul_of_nonneg_left product (show 0 ≤ secondConstant * epsilon by dsimp only [epsilon]; positivity)
  have scalar : firstConstant * (omega * epsilon) * 1 + secondConstant * epsilon * omega ≤ constant * omega * epsilon := by
    dsimp only [constant]
    nlinarith [show 0 ≤ omega * epsilon by dsimp only [epsilon]; positivity]
  exact (divided.trans (add_le_add firstTerm secondTerm)).trans scalar

end EulerNonuniqueness.Paper
