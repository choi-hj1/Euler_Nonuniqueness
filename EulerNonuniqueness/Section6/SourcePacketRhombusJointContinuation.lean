import EulerNonuniqueness.Section6.SourcePacketRhombusNeutralImprovement
import EulerNonuniqueness.Section5.CascadeRhombusDiagonalPrefix
import EulerNonuniqueness.Section6.MovingComplexMomentContinuity
import EulerNonuniqueness.Section1.UniformTransportScaleSmallness
import EulerNonuniqueness.General.StrictPrefixBootstrap

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000

theorem Scales.eventually_rhombus_joint_diagonal_neutral_continuation (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {scaleRoot boundaryConstant : ℝ}
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant) :
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant shapeRadius factor monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared,
    threshold ≤ 1 / 2 → factor ≤ 1 / 8 →
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
    ∀ time ∈ Icc 0 finish,
      |diagonalDifference prepared.trajectory.movingFamily.patchMotion time index /
        ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2 - 1| ≤ 1 / 4 ∧
      ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index‖ <
        ({scales with frequency := frequency} : Scales).length (index.val + 1) / 128 := by
  have boundaryLimit : Tendsto (fun frequency : ℝ => (boundaryConstant / scaleRoot ^ 2) * frequency⁻¹ ^ 2)
      atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
      ((tendsto_inv_atTop_zero : Tendsto (fun frequency : ℝ => frequency⁻¹) atTop (𝓝 0)).pow 2).const_mul
        (boundaryConstant / scaleRoot ^ 2)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_rhombus_neutral_strict_improvement amplitudePositive ratioBound alphaPositive,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num),
    scales.eventually_omega_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    boundaryLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    scales.eventually_reference_diagonal_numeric ratioBound alphaPositive (cascadeRhombusImpulseConstant / 2)
      (boundaryConstant / scaleRoot ^ 2)]
    with frequency frequencyLarge neutralImprovement geometry transport strainSmall hessianSmall boundarySmall numeric
  intro orbit sectionTime phase dipoleAngle threshold referenceConstant shapeRadius factor monitor count prepared path
    thresholdSmall factorSmall index nonterminal finish finishNonnegative finishBound radialSmall
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyLarge
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith
  have lengthPositive := changed.length_pos (index.val + 1)
  have lengthSquarePositive := sq_pos_of_pos lengthPositive
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have omegaBound := changed.omega_ge_frequency frequencyPositive (by dsimp only [changed]; linarith) (index.val + 1)
  have rhoSmall : boundaryConstant / (scaleRoot ^ 2 * changed.omega (index.val + 1) ^ 2) ≤ 1 / 16 := by
    have inverseBound := pow_le_pow_left₀ (inv_nonneg.mpr omegaPositive.le)
      (inv_anti₀ frequencyPositive omegaBound) 2
    have actual := (mul_le_mul_of_nonneg_left inverseBound
      (show 0 ≤ boundaryConstant / scaleRoot ^ 2 by positivity)).trans boundarySmall.le
    convert actual using 1
    field_simp [rootPositive.ne', omegaPositive.ne']
    <;> ring
  have numericBound : cascadeRhombusImpulseConstant * (changed.strain + changed.hessian) +
      48 * (boundaryConstant / scaleRoot ^ 2) ^ 2 / (changed.amplitude * changed.frequency ^ 7) ≤ 1 / 4 := by
    convert numeric.le using 1 <;> dsimp only [changed] <;> ring
  have omegaLength : changed.omega (index.val + 1) * changed.length (index.val + 1) ≤ 1 :=
    (transport (index.val + 1)).le.trans (by simpa only [one_mul] using scales.location_le_one (index.val + 1))
  have initial := prepared.nonterminal_initial_invariants amplitudePositive frequencyPositive ratioPositive thresholdSmall index nonterminal
  have initialNeutral : centroidAsymmetry motion 0 index = 0 := initial.1
  have initialDiagonal : diagonalDifference motion 0 index = changed.length (index.val + 1) ^ 2 := initial.2.1
  have positiveContinuous : Continuous (fun time => positiveHalfDiagonal motion time index) :=
    ((prepared.trajectory.movingFamily.patchCentroid_continuous index 0).sub
      (prepared.trajectory.movingFamily.patchCentroid_continuous index 1)).div_const 2
  have negativeContinuous : Continuous (fun time => negativeHalfDiagonal motion time index) :=
    ((prepared.trajectory.movingFamily.patchCentroid_continuous index 2).sub
      (prepared.trajectory.movingFamily.patchCentroid_continuous index 3)).div_const 2
  have differenceContinuous : Continuous (fun time => diagonalDifference motion time index) :=
    (positiveContinuous.norm.pow 2).sub (negativeContinuous.norm.pow 2)
  have neutralContinuous : Continuous (fun time => centroidAsymmetry motion time index) :=
    ((((prepared.trajectory.movingFamily.patchCentroid_continuous index 0).add
      (prepared.trajectory.movingFamily.patchCentroid_continuous index 1)).sub
      (prepared.trajectory.movingFamily.patchCentroid_continuous index 2)).sub
      (prepared.trajectory.movingFamily.patchCentroid_continuous index 3)).div_const 4
  let observable : Fin 3 → ℝ → ℝ := fun label time =>
    if label = 0 then changed.length (index.val + 1) ^ 2 / 2 - diagonalDifference motion time index
    else if label = 1 then diagonalDifference motion time index - 2 * changed.length (index.val + 1) ^ 2
    else ‖centroidAsymmetry motion time index‖ - changed.length (index.val + 1) / 64
  have continuous (label : Fin 3) : ContinuousOn (observable label) (Icc 0 finish) := by
    fin_cases label
    · simpa only [observable, ↓reduceIte] using (continuous_const.sub differenceContinuous).continuousOn
    · simpa only [observable, ↓reduceIte] using (differenceContinuous.sub continuous_const).continuousOn
    · simpa only [observable, ↓reduceIte] using (neutralContinuous.norm.sub continuous_const).continuousOn
  have initialStrict (label : Fin 3) : observable label 0 < 0 := by
    fin_cases label <;> simp [observable, initialNeutral, initialDiagonal] <;> nlinarith
  have confined := EulerNonuniqueness.General.finite_strictly_negative_of_strict_prefix_improvement continuous initialStrict (by
    intro contact contactInside closed _
    have lower (time : ℝ) (inside : time ∈ Icc 0 contact) : changed.length (index.val + 1) ^ 2 / 2 ≤
        diagonalDifference motion time index := by
      have bound := closed time inside 0
      change changed.length (index.val + 1) ^ 2 / 2 - diagonalDifference motion time index ≤ 0 at bound
      linarith
    have upper (time : ℝ) (inside : time ∈ Icc 0 contact) : diagonalDifference motion time index ≤
        2 * changed.length (index.val + 1) ^ 2 := by
      have bound := closed time inside 1
      change diagonalDifference motion time index - 2 * changed.length (index.val + 1) ^ 2 ≤ 0 at bound
      linarith
    have neutral (time : ℝ) (inside : time ∈ Icc 0 contact) : ‖centroidAsymmetry motion time index‖ ≤
        changed.length (index.val + 1) / 64 := by
      have bound := closed time inside 2
      change ‖centroidAsymmetry motion time index‖ - changed.length (index.val + 1) / 64 ≤ 0 at bound
      linarith
    have radial := fun time (inside : time ∈ Icc 0 contact) => radialSmall time ⟨inside.1, inside.2.trans contactInside.2⟩
    have diagonal := path.rhombus_diagonal_prefix_quarter_bound amplitudePositive frequencyLarge ratioBound alphaPositive
      thresholdSmall factorSmall rootPositive boundaryNonnegative index nonterminal contactInside.1
      (contactInside.2.trans finishBound) lower upper radial neutral (geometry (index.val + 1)).2.2.1
      (by simpa only [one_mul] using (geometry (index.val + 1)).2.1)
      (fun source => (geometry (source.val + 1)).2.2.2) omegaLength strainSmall.le hessianSmall.le rhoSmall numericBound
    have neutralStrict := neutralImprovement prepared path thresholdSmall factorSmall index nonterminal contact contactInside.1
      (contactInside.2.trans finishBound) lower upper radial neutral
    have endpoint := diagonal contact ⟨contactInside.1, le_rfl⟩
    intro label
    fin_cases label
    · change changed.length (index.val + 1) ^ 2 / 2 - diagonalDifference motion contact index < 0
      have ratioLower : (3 / 4 : ℝ) ≤ diagonalDifference motion contact index / changed.length (index.val + 1) ^ 2 := by
        linarith [(abs_le.mp endpoint).1]
      have multiplied := (le_div_iff₀ lengthSquarePositive).mp ratioLower
      nlinarith
    · change diagonalDifference motion contact index - 2 * changed.length (index.val + 1) ^ 2 < 0
      have ratioUpper : diagonalDifference motion contact index / changed.length (index.val + 1) ^ 2 ≤ (5 / 4 : ℝ) := by
        linarith [(abs_le.mp endpoint).2]
      have multiplied := (div_le_iff₀ lengthSquarePositive).mp ratioUpper
      nlinarith
    · change ‖centroidAsymmetry motion contact index‖ - changed.length (index.val + 1) / 64 < 0
      nlinarith)
  have lower (time : ℝ) (inside : time ∈ Icc 0 finish) : changed.length (index.val + 1) ^ 2 / 2 ≤
      diagonalDifference motion time index := by
    have bound := confined time inside 0
    change changed.length (index.val + 1) ^ 2 / 2 - diagonalDifference motion time index < 0 at bound
    linarith
  have upper (time : ℝ) (inside : time ∈ Icc 0 finish) : diagonalDifference motion time index ≤
      2 * changed.length (index.val + 1) ^ 2 := by
    have bound := confined time inside 1
    change diagonalDifference motion time index - 2 * changed.length (index.val + 1) ^ 2 < 0 at bound
    linarith
  have neutral (time : ℝ) (inside : time ∈ Icc 0 finish) : ‖centroidAsymmetry motion time index‖ ≤
      changed.length (index.val + 1) / 64 := by
    have bound := confined time inside 2
    change ‖centroidAsymmetry motion time index‖ - changed.length (index.val + 1) / 64 < 0 at bound
    linarith
  have diagonal := path.rhombus_diagonal_prefix_quarter_bound amplitudePositive frequencyLarge ratioBound alphaPositive
    thresholdSmall factorSmall rootPositive boundaryNonnegative index nonterminal finishNonnegative finishBound
    lower upper radialSmall neutral (geometry (index.val + 1)).2.2.1
    (by simpa only [one_mul] using (geometry (index.val + 1)).2.1)
    (fun source => (geometry (source.val + 1)).2.2.2) omegaLength strainSmall.le hessianSmall.le rhoSmall numericBound
  intro time inside
  refine ⟨diagonal time inside, ?_⟩
  exact neutralImprovement prepared path thresholdSmall factorSmall index nonterminal time inside.1
    (inside.2.trans finishBound)
    (fun current member => lower current ⟨member.1, member.2.trans inside.2⟩)
    (fun current member => upper current ⟨member.1, member.2.trans inside.2⟩)
    (fun current member => radialSmall current ⟨member.1, member.2.trans inside.2⟩)
    (fun current member => neutral current ⟨member.1, member.2.trans inside.2⟩)

end EulerNonuniqueness.Paper
