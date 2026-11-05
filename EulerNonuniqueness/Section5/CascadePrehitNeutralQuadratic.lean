import EulerNonuniqueness.Section6.SourcePacketRhombusJointContinuation
import EulerNonuniqueness.Section4.UniversalReferenceNeutralHistory

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem exists_uniform_cascade_prehit_neutral_quadratic_bound :
    ∃ memory ≥ (1 : ℝ), ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ {scaleRoot boundaryConstant threshold referenceConstant : ℝ},
      0 < scaleRoot → 0 ≤ boundaryConstant → threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
      ∀ᶠ frequency : ℝ in atTop,
      ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
        {shapeRadius factor monitor : ℝ} {count : ℕ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, factor ≤ 1 / 8 →
      ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
      (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
      ∀ time ∈ Icc 0 finish,
      let changed : Scales := {scales with frequency := frequency}
      ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index‖ ≤
          memory * changed.hessian * changed.length (index.val + 1) ^ 2 ∧
      ‖centroidAsymmetry prepared.reference time index‖ ≤
          memory * changed.hessian * changed.length (index.val + 1) ^ 2 := by
  obtain ⟨referenceMemory, referenceMemoryOne, referenceHistory⟩ := exists_uniform_paper_reference_neutral_history
  let alternativeMemory := (497664 / Real.pi) * Real.exp (1152 / Real.pi)
  let memory := 1 + referenceMemory + alternativeMemory
  have alternativeNonnegative : 0 ≤ alternativeMemory := by dsimp only [alternativeMemory]; positivity
  have referenceNonnegative : 0 ≤ referenceMemory := le_trans (by norm_num) referenceMemoryOne
  have memoryOne : 1 ≤ memory := by dsimp only [memory]; linarith
  refine ⟨memory, memoryOne, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive scaleRoot boundaryConstant threshold referenceConstant
    rootPositive boundaryNonnegative thresholdSmall referenceConstantNonnegative
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_rhombus_joint_diagonal_neutral_continuation amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num),
    referenceHistory scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceConstantNonnegative,
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency frequencyBound joint geometry reference strainSmall
  intro orbit sectionTime phase dipoleAngle shapeRadius factor monitor count prepared path factorSmall index nonterminal
    finish finishNonnegative finishBound radialSmall time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have lengthPositive := changed.length_pos (index.val + 1)
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have jointData := joint prepared path (thresholdSmall.trans (by norm_num)) factorSmall index nonterminal
    finish finishNonnegative finishBound radialSmall
  have lower (current : ℝ) (member : current ∈ Icc 0 finish) : changed.length (index.val + 1) ^ 2 / 2 ≤
      diagonalDifference prepared.trajectory.movingFamily.patchMotion current index := by
    have actual := (jointData current member).1
    have inequality := neg_abs_le (diagonalDifference prepared.trajectory.movingFamily.patchMotion current index /
      changed.length (index.val + 1) ^ 2 - 1)
    have squaredPositive := sq_pos_of_pos lengthPositive
    have ratioLower : (3 / 4 : ℝ) ≤ diagonalDifference prepared.trajectory.movingFamily.patchMotion current index /
        changed.length (index.val + 1) ^ 2 := by linarith
    have multiplied := (le_div_iff₀ squaredPositive).mp ratioLower
    nlinarith
  have upper (current : ℝ) (member : current ∈ Icc 0 finish) :
      diagonalDifference prepared.trajectory.movingFamily.patchMotion current index ≤ 2 * changed.length (index.val + 1) ^ 2 := by
    have actual := (jointData current member).1
    have inequality := le_abs_self (diagonalDifference prepared.trajectory.movingFamily.patchMotion current index /
      changed.length (index.val + 1) ^ 2 - 1)
    have squaredPositive := sq_pos_of_pos lengthPositive
    have ratioUpper : diagonalDifference prepared.trajectory.movingFamily.patchMotion current index /
        changed.length (index.val + 1) ^ 2 ≤ (5 / 4 : ℝ) := by linarith
    have multiplied := (div_le_iff₀ squaredPositive).mp ratioUpper
    nlinarith
  have asymmetry (current : ℝ) (member : current ∈ Icc 0 finish) :
      ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion current index‖ ≤ changed.length (index.val + 1) / 64 := by
    have actual := (jointData current member).2
    linarith
  have actualHistory := path.rhombus_neutral_prefix_bound amplitudePositive frequencyBound ratioBound alphaPositive
    (thresholdSmall.trans (by norm_num)) factorSmall index nonterminal finishNonnegative finishBound lower upper radialSmall asymmetry
    (geometry (index.val + 1)).2.2.1 (by simpa only [one_mul] using (geometry (index.val + 1)).2.1)
    (fun source => (geometry (source.val + 1)).2.2.2)
  have timeOne : time ≤ 1 := inside.2.trans (finishBound.trans path.stopBound)
  have exponential : Real.exp (((1152 / Real.pi) * changed.strain) * time) ≤ Real.exp (1152 / Real.pi) := by
    apply Real.exp_le_exp.mpr
    have first := mul_le_mul_of_nonneg_left timeOne (show 0 ≤ (1152 / Real.pi) * changed.strain by positivity)
    have second := mul_le_mul_of_nonneg_left strainSmall.le (show 0 ≤ 1152 / Real.pi by positivity)
    simp only [mul_one] at first second
    exact first.trans second
  have alternative := (actualHistory time inside).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left timeOne
      (show 0 ≤ (497664 / Real.pi) * changed.hessian * changed.length (index.val + 1) ^ 2 by positivity))
      exponential (Real.exp_pos _).le (by positivity))
  have alternative' : ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index‖ ≤
      alternativeMemory * changed.hessian * changed.length (index.val + 1) ^ 2 :=
    alternative.trans_eq (by dsimp only [alternativeMemory]; ring)
  have referenceInside : time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, by linarith [inside.2, finishBound, path.stopBound]⟩
  have reference' := (reference _ prepared.referenceWitness.evolution prepared.referenceWitness.initial
    prepared.referenceWitness.coarse time referenceInside index).2
  have factorNonnegative : 0 ≤ changed.hessian * changed.length (index.val + 1) ^ 2 := by positivity
  constructor
  · exact alternative'.trans (by
      have bound : alternativeMemory ≤ memory := by dsimp only [memory]; linarith
      nlinarith [mul_le_mul_of_nonneg_right bound factorNonnegative])
  · have bound : referenceMemory ≤ memory := by dsimp only [memory]; linarith
    have reference'' : ‖centroidAsymmetry prepared.reference time index‖ ≤
        referenceMemory * changed.hessian * changed.length (index.val + 1) ^ 2 := by
      simpa only [prepared.referenceIdentity] using reference'
    exact reference''.trans (by nlinarith [mul_le_mul_of_nonneg_right bound factorNonnegative])

end EulerNonuniqueness.Paper
