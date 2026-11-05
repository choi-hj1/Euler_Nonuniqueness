import EulerNonuniqueness.Section6.SourcePacketUniformReceiverFieldGeometry
import EulerNonuniqueness.Section4.ReferencePhaseKinematics

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000

theorem Scales.eventually_actual_receiver_diagonal_small (scales : Scales)
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
    |referenceDilation {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion index time - 1| ≤ tolerance := by
  have fieldLimit := ((scales.strain_tendsto_zero ratioBound alphaPositive).add
    (scales.hessian_tendsto_zero ratioBound alphaPositive)).const_mul cascadeRhombusImpulseConstant
  have powerLimit := (tendsto_inv_atTop_zero : Tendsto (fun frequency : ℝ => frequency⁻¹) atTop (𝓝 0)).pow 7
  have totalLimit := fieldLimit.add (powerLimit.const_mul
    (48 * (boundaryConstant / scaleRoot ^ 2) ^ 2 / scales.amplitude))
  simp only [add_zero, mul_zero, zero_pow (by norm_num : (7 : ℕ) ≠ 0)] at totalLimit
  have boundaryLimit : Tendsto (fun frequency : ℝ => (boundaryConstant / scaleRoot ^ 2) * frequency⁻¹ ^ 2)
      atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
      ((tendsto_inv_atTop_zero : Tendsto (fun frequency : ℝ => frequency⁻¹) atTop (𝓝 0)).pow 2).const_mul
        (boundaryConstant / scaleRoot ^ 2)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_rhombus_joint_diagonal_neutral_continuation amplitudePositive ratioBound alphaPositive
      rootPositive boundaryNonnegative,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num),
    scales.eventually_omega_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    boundaryLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    totalLimit.eventually (eventually_lt_nhds tolerancePositive)]
    with frequency frequencyOne joint geometry transport strainSmall hessianSmall boundarySmall totalSmall
  intro orbit sectionTime phase dipoleAngle threshold referenceConstant shapeRadius factor monitor count prepared path
    thresholdSmall factorSmall index nonterminal finish finishNonnegative finishBound radialSmall time inside
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
  have rhoSmall : boundaryConstant / (scaleRoot ^ 2 * changed.omega (index.val + 1) ^ 2) ≤ 1 / 16 := by
    have inverseBound := pow_le_pow_left₀ (inv_nonneg.mpr omegaPositive.le) (inv_anti₀ frequencyPositive omegaBound) 2
    have actual := (mul_le_mul_of_nonneg_left inverseBound
      (show 0 ≤ boundaryConstant / scaleRoot ^ 2 by positivity)).trans boundarySmall.le
    convert actual using 1 <;> field_simp [rootPositive.ne', omegaPositive.ne'] <;> ring
  have impulse := path.rhombus_impulse_prefix_bound amplitudePositive frequencyOne ratioBound alphaPositive
    thresholdSmall factorSmall index nonterminal finishNonnegative finishBound lower upper radialSmall
    (fun current member => by linarith [(controls current member).2])
    (geometry (index.val + 1)).2.2.1 (by simpa using (geometry (index.val + 1)).2.1)
    (fun source => (geometry (source.val + 1)).2.2.2)
    ((transport (index.val + 1)).le.trans (by simpa using changed.location_le_one (index.val + 1)))
    strainSmall.le hessianSmall.le
  have timeInside : time ∈ Icc 0 path.stop := ⟨inside.1, inside.2.trans finishBound⟩
  have inertia := path.evolution.reference_diagonal_impulse_error timeInside amplitudePositive frequencyPositive ratioPositive
    index (path.boundary time timeInside index) (by positivity) rhoSmall
  have deformation := changed.reference_diagonal_deformation_cost_le amplitudePositive frequencyPositive
    (by change 1 ≤ scales.ratio; linarith) (index.val + 1) (by positivity)
    (show boundaryConstant / (scaleRoot ^ 2 * changed.omega (index.val + 1) ^ 2) ≤
      (boundaryConstant / scaleRoot ^ 2) / changed.omega (index.val + 1) ^ 2 by rw [div_div])
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
  have impulseNonnegative : 0 ≤ cascadeRhombusImpulseConstant * (changed.strain + changed.hessian) := by
    unfold cascadeRhombusImpulseConstant cascadeRhombusMemoryConstant; positivity
  have numeric : cascadeRhombusImpulseConstant * (changed.strain + changed.hessian) +
      48 * (boundaryConstant / scaleRoot ^ 2) ^ 2 / (changed.amplitude * changed.frequency ^ 7) < tolerance := by
    convert totalSmall using 1 <;> dsimp only [changed] <;> simp only [div_eq_mul_inv, mul_inv_rev, inv_pow] <;> ring
  exact (inertia.trans (add_le_add (impulse time inside) deformation)).trans
    ((add_le_add_right (mul_le_of_le_one_right impulseNonnegative
      (inside.2.trans (finishBound.trans path.stopBound))) _).trans numeric.le)

end EulerNonuniqueness.Paper
