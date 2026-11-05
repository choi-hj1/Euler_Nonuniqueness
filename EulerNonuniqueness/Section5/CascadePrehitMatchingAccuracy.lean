import EulerNonuniqueness.Section5.CascadeRhombusDiagonalNumeric
import EulerNonuniqueness.Section6.SourcePacketRhombusJointContinuation

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_material_prehit_matching_accuracy (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {scaleRoot boundaryConstant tolerance : ℝ}
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
    (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant shapeRadius factor monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, threshold ≤ 1 / 2 → factor ≤ 1 / 8 →
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
    ∀ time ∈ Icc 0 finish,
      |diagonalDifference prepared.trajectory.movingFamily.patchMotion time index /
        ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2 - 1| < tolerance ∧
      ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index‖ /
        ({scales with frequency := frequency} : Scales).length (index.val + 1) < tolerance := by
  have inversePower := (tendsto_inv_atTop_zero : Tendsto (fun frequency : ℝ => frequency⁻¹) atTop (𝓝 0)).pow 7
  have deformationLimit := inversePower.const_mul (48 * (boundaryConstant / scaleRoot ^ 2) ^ 2 / scales.amplitude)
  have fieldLimit := ((scales.strain_tendsto_zero ratioBound alphaPositive).add
    (scales.hessian_tendsto_zero ratioBound alphaPositive)).const_mul cascadeRhombusImpulseConstant
  have totalLimit := fieldLimit.add deformationLimit
  simp only [add_zero, mul_zero, zero_pow (by norm_num : (7 : ℕ) ≠ 0)] at totalLimit
  have numeric : ∀ᶠ frequency : ℝ in atTop,
      cascadeRhombusImpulseConstant * (({scales with frequency := frequency} : Scales).strain +
        ({scales with frequency := frequency} : Scales).hessian) +
      48 * (boundaryConstant / scaleRoot ^ 2) ^ 2 / (scales.amplitude * frequency ^ 7) < tolerance := by
    convert totalLimit.eventually (eventually_lt_nhds tolerancePositive) using 1
    simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
    congr 1
    ext frequency
    ring
  have boundaryLimit : Tendsto (fun frequency : ℝ => (boundaryConstant / scaleRoot ^ 2) * frequency⁻¹ ^ 2)
      atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
      ((tendsto_inv_atTop_zero : Tendsto (fun frequency : ℝ => frequency⁻¹) atTop (𝓝 0)).pow 2).const_mul
        (boundaryConstant / scaleRoot ^ 2)
  have neutralLimit := (scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul cascadeRhombusMemoryConstant
  simp only [mul_zero] at neutralLimit
  filter_upwards [eventually_ge_atTop (1 : ℝ), numeric,
    neutralLimit.eventually (eventually_lt_nhds tolerancePositive),
    scales.eventually_rhombus_joint_diagonal_neutral_continuation amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num),
    scales.eventually_omega_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    boundaryLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 16))]
    with frequency frequencyOne numeric neutralSmall joint geometry transport strainSmall hessianSmall boundarySmall
  intro orbit sectionTime phase dipoleAngle threshold referenceConstant shapeRadius factor monitor count prepared path
    thresholdSmall factorSmall index nonterminal finish finishNonnegative finishBound radialSmall
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have lengthPositive := changed.length_pos (index.val + 1)
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have omegaBound := changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith) (index.val + 1)
  have actual := joint prepared path thresholdSmall factorSmall index nonterminal finish finishNonnegative finishBound radialSmall
  have lower (time : ℝ) (member : time ∈ Icc 0 finish) : changed.length (index.val + 1) ^ 2 / 2 ≤
      diagonalDifference prepared.trajectory.movingFamily.patchMotion time index := by
    have diagonal := (abs_le.mp (actual time member).1).1
    have scaled := (le_div_iff₀ (sq_pos_of_pos lengthPositive)).mp (by linarith :
      (1 / 2 : ℝ) ≤ diagonalDifference prepared.trajectory.movingFamily.patchMotion time index / changed.length (index.val + 1) ^ 2)
    linarith
  have upper (time : ℝ) (member : time ∈ Icc 0 finish) : diagonalDifference prepared.trajectory.movingFamily.patchMotion time index ≤
      2 * changed.length (index.val + 1) ^ 2 := by
    have diagonal := (abs_le.mp (actual time member).1).2
    exact (div_le_iff₀ (sq_pos_of_pos lengthPositive)).mp (by linarith)
  have neutral (time : ℝ) (member : time ∈ Icc 0 finish) : ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index‖ ≤
      changed.length (index.val + 1) / 64 := by linarith [(actual time member).2]
  have lengthSmall := (geometry (index.val + 1)).2.2.1
  have radiusSmall : changed.radius (index.val + 1) ≤ changed.length (index.val + 1) / 1000 := by
    simpa only [one_mul] using (geometry (index.val + 1)).2.1
  have radiusLocation (source : Fin count) : changed.radius (source.val + 1) ≤ changed.location (source.val + 1) / 1000 := by
    have radius := (geometry (source.val + 1)).2.1
    have length := (geometry (source.val + 1)).2.2.1
    simp only [one_mul] at radius
    linarith [changed.location_pos (source.val + 1)]
  have omegaLength : changed.omega (index.val + 1) * changed.length (index.val + 1) ≤ 1 :=
    (transport (index.val + 1)).le.trans (by simpa only [one_mul] using changed.location_le_one (index.val + 1))
  have rhoSmall : boundaryConstant / (scaleRoot ^ 2 * changed.omega (index.val + 1) ^ 2) ≤ 1 / 16 := by
    have inverseBound := pow_le_pow_left₀ (inv_nonneg.mpr omegaPositive.le) (inv_anti₀ frequencyPositive omegaBound) 2
    have bound := (mul_le_mul_of_nonneg_left inverseBound
      (show 0 ≤ boundaryConstant / scaleRoot ^ 2 by positivity)).trans boundarySmall.le
    convert bound using 1
    field_simp [rootPositive.ne', omegaPositive.ne']
    <;> ring
  have diagonal := path.rhombus_diagonal_prefix_numeric_bound amplitudePositive frequencyOne ratioBound alphaPositive
    thresholdSmall factorSmall rootPositive boundaryNonnegative index nonterminal finishNonnegative finishBound
    lower upper radialSmall neutral lengthSmall radiusSmall radiusLocation omegaLength strainSmall.le hessianSmall.le rhoSmall
  have history := path.rhombus_neutral_prefix_bound amplitudePositive frequencyOne ratioBound alphaPositive
    thresholdSmall factorSmall index nonterminal finishNonnegative finishBound lower upper radialSmall neutral
    lengthSmall radiusSmall radiusLocation
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
  intro time member
  refine ⟨(diagonal time member).trans_lt numeric, ?_⟩
  have timeBound : time ≤ 1 := member.2.trans (finishBound.trans path.stopBound)
  have historyBound : ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index‖ ≤
      cascadeRhombusMemoryConstant * changed.hessian * changed.length (index.val + 1) ^ 2 := by
    apply (history time member).trans
    calc
      _ ≤ (497664 / Real.pi) * changed.hessian * changed.length (index.val + 1) ^ 2 * 1 *
          Real.exp (((1152 / Real.pi) * 1) * 1) := by gcongr; exact member.1
      _ = _ := by unfold cascadeRhombusMemoryConstant; ring
  have quotientBound : ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index‖ /
      changed.length (index.val + 1) ≤ cascadeRhombusMemoryConstant * changed.hessian * changed.length (index.val + 1) := by
    apply (div_le_iff₀ lengthPositive).mpr
    exact historyBound.trans_eq (by ring)
  have memoryNonnegative : 0 ≤ cascadeRhombusMemoryConstant * changed.hessian := by
    unfold cascadeRhombusMemoryConstant
    positivity
  exact (quotientBound.trans (mul_le_of_le_one_right memoryNonnegative
    (changed.length_le_one frequencyPositive ratioPositive _))).trans_lt neutralSmall

end EulerNonuniqueness.Paper
