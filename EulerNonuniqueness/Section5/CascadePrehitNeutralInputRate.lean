import EulerNonuniqueness.Section5.CascadeNeutralStrongNormalization
import EulerNonuniqueness.Section5.CascadeQuadrupoleForeignHeadTail
import EulerNonuniqueness.Section4.UniversalReferenceNeutralHistory

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem exists_uniform_cascade_prehit_firstMoment_input_rate :
    ∃ memory ≥ (1 : ℝ), ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < factor → factor ≤ 1 / 8 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count, index.val + 1 < count →
      ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
      (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
      ∀ time ∈ Icc 0 finish,
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      let radius := factor / 39321600 * changed.location (index.val + 1)
      let difference := ∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time radius power -
        quadrupoleExteriorCoefficient changed second index time radius power‖
      ‖relativeFirstMomentExternalVelocity changed first second index time‖ ≤
        (96 / Real.pi * (2304 * changed.strain)) *
          (‖relativeNormalizedFirstMoment changed first second index time‖ +
          (24 * changed.location (index.val + 1) / radius) *
            ‖quadrupoleNormalizedCentroidOffsets first index time (changed.length (index.val + 1)) -
              quadrupoleNormalizedCentroidOffsets second index time (changed.length (index.val + 1))‖) +
        (4 * memory * changed.hessian + 36 * changed.location (index.val + 1) / radius) * difference +
        (4 * changed.location (index.val + 1) / changed.length (index.val + 1) ^ 2) *
          ‖quadrupoleExternalReceiverAverage changed first index time - quadrupoleExternalReceiverAverage changed second index time‖ := by
  obtain ⟨memory, memoryOne, neutralHistory⟩ := exists_uniform_paper_reference_neutral_history
  refine ⟨memory, memoryOne, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor
    boundaryConstant thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_cascade_prehit_firstMoment_rate amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_quadrupole_foreign_head_tail amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive (factorSmall.trans (by norm_num)),
    neutralHistory scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative]
    with frequency frequencyBound rate coefficientBounds referenceBound
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let radius := factor / 39321600 * changed.location (index.val + 1)
  let weight := 4 * changed.location (index.val + 1) / changed.length (index.val + 1) ^ 2
  let difference := ∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time radius power -
    quadrupoleExteriorCoefficient changed second index time radius power‖
  have fullInside : time ∈ Icc 0 path.stop := ⟨inside.1, inside.2.trans finishBound⟩
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have locationPositive := changed.location_pos (index.val + 1)
  have lengthPositive := changed.length_pos (index.val + 1)
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have weightNonnegative : 0 ≤ weight := by dsimp only [weight]; positivity
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg (fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (changed.location_pos _).le _))
  have firstCoefficients := coefficientBounds count phase dipoleAngle prepared path time fullInside index 0
  have secondCoefficients := coefficientBounds count phase dipoleAngle prepared path time fullInside index 1
  have differenceSummable : Summable (fun power : ℕ =>
      ‖quadrupoleExteriorCoefficient changed first index time radius power -
        quadrupoleExteriorCoefficient changed second index time radius power‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_sub_le _ _)
      (firstCoefficients.1.add secondCoefficients.1)
  have differenceBounds := Section6.coefficient_norm_head_tail_le_tsum
    (fun power => quadrupoleExteriorCoefficient changed first index time radius power -
      quadrupoleExteriorCoefficient changed second index time radius power) differenceSummable
  have referenceInside : time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, by linarith [inside.2, finishBound, path.stopBound]⟩
  have referenceNeutral := (referenceBound _ prepared.referenceWitness.evolution prepared.referenceWitness.initial
    prepared.referenceWitness.coarse time referenceInside index).2
  have weightedReference : weight * ‖centroidAsymmetry second time index‖ ≤ 4 * memory * changed.hessian := by
    have actual : ‖centroidAsymmetry second time index‖ ≤ memory * changed.hessian * changed.length (index.val + 1) ^ 2 := by
      simpa only [second, prepared.referenceIdentity] using referenceNeutral
    calc
      weight * ‖centroidAsymmetry second time index‖ ≤
          weight * (memory * changed.hessian * changed.length (index.val + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left actual weightNonnegative
      _ = (4 * memory * changed.hessian) * changed.location (index.val + 1) := by
        dsimp only [weight]
        field_simp [lengthPositive.ne']
        <;> ring
      _ ≤ 4 * memory * changed.hessian :=
        mul_le_of_le_one_right (by positivity) (changed.location_le_one _)
  have actual := (rate count phase dipoleAngle prepared path index nonterminal finish finishNonnegative finishBound
    radialSmall time inside).2
  rw [quadrupoleNeutralSeriesEnvelope_strong_normalization changed first second index time radiusPositive] at actual
  have firstTerm := mul_le_mul_of_nonneg_right firstCoefficients.2.1
    (norm_nonneg (relativeNormalizedFirstMoment changed first second index time))
  have secondTerm := (mul_le_mul_of_nonneg_left weightedReference
    (norm_nonneg (quadrupoleExteriorCoefficient changed first index time radius 0 -
      quadrupoleExteriorCoefficient changed second index time radius 0))).trans
      (mul_le_mul_of_nonneg_right differenceBounds.1 (by positivity : 0 ≤ 4 * memory * changed.hessian))
  have thirdTerm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left firstCoefficients.2.2
      (show 0 ≤ 24 * changed.location (index.val + 1) / radius by positivity))
    (norm_nonneg (quadrupoleNormalizedCentroidOffsets first index time (changed.length (index.val + 1)) -
      quadrupoleNormalizedCentroidOffsets second index time (changed.length (index.val + 1))))
  have fourthTerm := mul_le_mul_of_nonneg_left differenceBounds.2
    (show 0 ≤ 36 * changed.location (index.val + 1) / radius by positivity)
  have total := actual.trans (add_le_add_right
    (add_le_add (add_le_add (add_le_add firstTerm secondTerm) thirdTerm) fourthTerm) _)
  convert total using 1 <;> dsimp only [weight, difference] <;> ring

end EulerNonuniqueness.Paper
