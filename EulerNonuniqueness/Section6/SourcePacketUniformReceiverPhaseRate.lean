import EulerNonuniqueness.Section6.SourcePacketMaterialPhaseRate

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000

theorem Scales.exists_eventually_actual_receiver_phase_rate (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {scaleRoot boundaryConstant : ℝ}
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant) :
    ∃ constant ≥ (1 : ℝ), ∃ phaseRadius > (0 : ℝ),
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant shapeRadius factor monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, threshold ≤ 1 / 2 → factor ≤ 1 / 8 →
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
    ∀ time ∈ Icc 0 finish,
    |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
      |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 4 →
    |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
      |stableShape prepared.trajectory.movingFamily.patchMotion time index| < phaseRadius →
    |referencePhaseError {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion index time| ≤
      constant * ({scales with frequency := frequency} : Scales).omega (index.val + 1) *
        (|unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
          |stableShape prepared.trajectory.movingFamily.patchMotion time index|) +
      constant * (({scales with frequency := frequency} : Scales).strain +
        (({scales with frequency := frequency} : Scales).omega (index.val + 1))⁻¹ ^ 4) := by
  obtain ⟨internal, internalNonnegative, momentRadius, momentRadiusPositive, phaseConstant, phaseNonnegative,
    phaseRadius, phaseRadiusPositive, estimate⟩ := exists_source_packet_material_phase_rate
  let memory := cascadeRhombusMemoryConstant
  let deformationBound := boundaryConstant / scaleRoot ^ 2
  let first := (2 * internal * memory ^ 2 + 4608) / Real.pi
  let second := (27648000000 + 226492416 / Real.pi) * deformationBound / scales.amplitude
  let constant := 1 + 2 * phaseConstant + first + second
  have memoryNonnegative : 0 ≤ memory := by unfold memory cascadeRhombusMemoryConstant; positivity
  have deformationBoundNonnegative : 0 ≤ deformationBound := by dsimp only [deformationBound]; positivity
  have firstNonnegative : 0 ≤ first := by dsimp only [first]; positivity
  have secondNonnegative : 0 ≤ second := by dsimp only [second]; positivity
  refine ⟨constant, by dsimp only [constant]; linarith, phaseRadius, phaseRadiusPositive, ?_⟩
  have boundaryLimit : Tendsto (fun frequency : ℝ => deformationBound * frequency⁻¹ ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
      ((tendsto_inv_atTop_zero : Tendsto (fun frequency : ℝ => frequency⁻¹) atTop (𝓝 0)).pow 2).const_mul deformationBound
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_rhombus_joint_diagonal_neutral_continuation amplitudePositive ratioBound alphaPositive
      rootPositive boundaryNonnegative,
    scales.eventually_actual_receiver_field_geometry amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num),
    scales.eventually_length_lt_location ratioBound alphaPositive
      (show 0 < momentRadius / (8 * (memory + 1)) by positivity),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    boundaryLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 16))]
    with frequency frequencyOne joint fields geometry lengths strainSmall hessianSmall boundarySmall
  intro orbit sectionTime phase dipoleAngle threshold referenceConstant shapeRadius factor monitor count prepared path
    thresholdSmall factorSmall index nonterminal finish finishNonnegative finishBound radialSmall time inside chartSmall chartPhaseSmall
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have lengthPositive := changed.length_pos (index.val + 1)
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have omegaBound := changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith) (index.val + 1)
  have controls := joint prepared path thresholdSmall factorSmall index nonterminal finish finishNonnegative finishBound radialSmall
  have lower (current : ℝ) (member : current ∈ Icc 0 finish) : changed.length (index.val + 1) ^ 2 / 2 ≤
      diagonalDifference motion current index := by
    have bound := (abs_le.mp (controls current member).1).1
    have multiplied := (le_div_iff₀ (sq_pos_of_pos lengthPositive)).mp
      (show (3 / 4 : ℝ) ≤ diagonalDifference motion current index / changed.length (index.val + 1) ^ 2 by linarith)
    nlinarith [sq_nonneg (changed.length (index.val + 1))]
  have upper (current : ℝ) (member : current ∈ Icc 0 finish) : diagonalDifference motion current index ≤
      2 * changed.length (index.val + 1) ^ 2 := by
    have bound := (abs_le.mp (controls current member).1).2
    have multiplied := (div_le_iff₀ (sq_pos_of_pos lengthPositive)).mp
      (show diagonalDifference motion current index / changed.length (index.val + 1) ^ 2 ≤ (5 / 4 : ℝ) by linarith)
    nlinarith [sq_nonneg (changed.length (index.val + 1))]
  have neutral := path.rhombus_neutral_prefix_bound amplitudePositive frequencyOne ratioBound alphaPositive
    thresholdSmall factorSmall index nonterminal finishNonnegative finishBound lower upper radialSmall
    (fun current member => by linarith [(controls current member).2])
    (geometry (index.val + 1)).2.2.1 (by simpa using (geometry (index.val + 1)).2.1)
    (fun source => (geometry (source.val + 1)).2.2.2)
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
  have timeOne : time ≤ 1 := inside.2.trans (finishBound.trans path.stopBound)
  have neutralBound : ‖centroidAsymmetry motion time index‖ ≤ memory * changed.length (index.val + 1) ^ 2 := by
    apply (neutral time inside).trans
    calc
      _ ≤ (497664 / Real.pi) * 1 * changed.length (index.val + 1) ^ 2 * 1 *
          Real.exp (((1152 / Real.pi) * 1) * 1) := by gcongr <;> exact inside.1
      _ = _ := by unfold memory cascadeRhombusMemoryConstant; ring
  have rhoSmall : boundaryConstant / (scaleRoot ^ 2 * changed.omega (index.val + 1) ^ 2) ≤ 1 / 16 := by
    have inverseBound := pow_le_pow_left₀ (inv_nonneg.mpr omegaPositive.le) (inv_anti₀ frequencyPositive omegaBound) 2
    have actual := (mul_le_mul_of_nonneg_left inverseBound deformationBoundNonnegative).trans boundarySmall.le
    convert actual using 1 <;> dsimp only [deformationBound] <;> field_simp [rootPositive.ne', omegaPositive.ne'] <;> ring
  have lengthSmall : changed.length (index.val + 1) < momentRadius / (8 * (memory + 1)) :=
    (lengths (index.val + 1)).trans_le (mul_le_of_le_one_right (by positivity) (changed.location_le_one _))
  have actual := estimate path amplitudePositive frequencyOne ratioBound alphaPositive time
    ⟨inside.1, inside.2.trans finishBound⟩ index
    (fields prepared path thresholdSmall factorSmall index nonterminal finish finishNonnegative finishBound radialSmall time inside)
    _ memory deformationBound (path.boundary time ⟨inside.1, inside.2.trans finishBound⟩ index)
    (by positivity) rhoSmall memoryNonnegative deformationBoundNonnegative
    (by dsimp only [deformationBound]; rw [div_div])
    (changed.length_le_one frequencyPositive ratioPositive _) hessianSmall.le (lower time inside) neutralBound lengthSmall
    chartSmall chartPhaseSmall
  have firstBound : first ≤ constant := by dsimp only [constant]; linarith
  have secondBound : second ≤ constant := by dsimp only [constant]; linarith
  have phaseBound : 2 * phaseConstant ≤ constant := by dsimp only [constant]; linarith
  apply actual.trans
  have firstScaled := mul_le_mul_of_nonneg_right firstBound strainNonnegative
  have secondScaled := mul_le_mul_of_nonneg_right secondBound (show 0 ≤ (changed.omega (index.val + 1))⁻¹ ^ 4 by positivity)
  have phaseScaled := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right phaseBound omegaPositive.le)
    (add_nonneg (abs_nonneg (unstableShape motion time index)) (abs_nonneg (stableShape motion time index)))
  convert add_le_add phaseScaled (add_le_add firstScaled secondScaled) using 1 <;>
    dsimp only [referenceOddForcingBudget, first, second, changed] <;>
    simp only [div_eq_mul_inv, inv_pow] <;> ring

end EulerNonuniqueness.Paper
