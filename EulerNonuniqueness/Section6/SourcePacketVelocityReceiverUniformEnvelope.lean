import EulerNonuniqueness.Section6.SourcePacketVelocityPhysicalBound

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.SourcePacketPhysicalGeometry

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

theorem actual_velocity_receiver_uniform_envelope
    {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)} {scales : Scales} {source : Fin count}
    {start horizon chartRadius : ℝ}
    (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius)
    {elapsed distance observerScale : ℝ} (inside : elapsed ∈ Icc 0 horizon)
    (distancePositive : 0 < distance) (distanceOne : distance ≤ 1)
    (observerNonnegative : 0 ≤ observerScale) (observerSmall : observerScale ≤ 2 * distance)
    (gapLower : distance / 2 ≤ geometry.gap)
    (observationLower : distance / 2 ≤ geometry.observationDistance)
    (widthSmall : geometry.halfWidth ≤ scales.length (source.val + 1)) :
    observerScale ^ 3 *
      ‖biotSavart (quadrupoleDensity scales family.patchMotion (start + elapsed) source) (geometry.location elapsed)‖ ≤
      4096 * scales.circulation (source.val + 1) *
        (‖geometry.firstSeparation elapsed + geometry.secondSeparation elapsed‖ +
          scales.length (source.val + 1) * ‖geometry.firstCenter elapsed - geometry.secondCenter elapsed‖ +
          scales.radius (source.val + 1) ^ 2) := by
  let circulation := scales.circulation (source.val + 1)
  let length := scales.length (source.val + 1)
  let radius := scales.radius (source.val + 1)
  let neutral := ‖geometry.firstSeparation elapsed + geometry.secondSeparation elapsed‖
  let separation := ‖geometry.firstCenter elapsed - geometry.secondCenter elapsed‖
  let observation := ‖geometry.location elapsed - (geometry.firstCenter elapsed + geometry.secondCenter elapsed) / 2‖
  have circulationPositive : 0 < circulation := scales.circulation_pos geometry.frequencyPositive geometry.ratioPositive _
  have lengthPositive : 0 < length := scales.length_pos _
  have neutralNonnegative : 0 ≤ neutral := norm_nonneg _
  have separationNonnegative : 0 ≤ separation := norm_nonneg _
  have halfPositive : 0 < distance / 2 := half_pos distancePositive
  have observationBound : distance / 2 ≤ observation :=
    observationLower.trans (geometry.observationLower elapsed inside)
  have observationPositive : 0 < observation := halfPositive.trans_le observationBound
  have neutralBound : neutral / observation ^ 2 ≤ 4 * neutral / distance ^ 2 := by
    have actual := div_le_div_of_nonneg_left neutralNonnegative (sq_pos_of_pos halfPositive)
      (pow_le_pow_left₀ halfPositive.le observationBound 2)
    exact actual.trans_eq (by field_simp; ring)
  have separationBound : geometry.halfWidth * separation / observation ^ 3 ≤
      8 * length * separation / distance ^ 3 := by
    have numerator := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right widthSmall separationNonnegative) (pow_nonneg observationPositive.le 3)
    have denominator := div_le_div_of_nonneg_left (mul_nonneg lengthPositive.le separationNonnegative)
      (pow_pos halfPositive 3) (pow_le_pow_left₀ halfPositive.le observationBound 3)
    exact (numerator.trans denominator).trans_eq (by field_simp; ring)
  have correctionBound : radius ^ 2 / geometry.gap ^ 3 ≤ 8 * radius ^ 2 / distance ^ 3 := by
    have actual := div_le_div_of_nonneg_left (sq_nonneg radius) (pow_pos halfPositive 3)
      (pow_le_pow_left₀ halfPositive.le gapLower 3)
    exact actual.trans_eq (by field_simp; ring)
  let upper := (40 * circulation / (2 * Real.pi)) *
    (4 * neutral / distance ^ 2 + 8 * length * separation / distance ^ 3) +
      (32 * circulation / Real.pi) * (8 * radius ^ 2 / distance ^ 3)
  have upperNonnegative : 0 ≤ upper := by dsimp only [upper]; positivity
  have physical := geometry.actual_velocity_far_field_bound inside
  have bounded := add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add neutralBound separationBound)
      (show 0 ≤ 40 * circulation / (2 * Real.pi) by positivity))
    (mul_le_mul_of_nonneg_left correctionBound (show 0 ≤ 32 * circulation / Real.pi by positivity))
  have velocityBound :
      ‖biotSavart (quadrupoleDensity scales family.patchMotion (start + elapsed) source) (geometry.location elapsed)‖ ≤ upper := by
    apply physical.trans
    convert bounded using 1
    dsimp only [upper, circulation, radius, neutral, observation, separation, length]
    ring
  have observerCube := pow_le_pow_left₀ observerNonnegative observerSmall 3
  have scaled := (mul_le_mul_of_nonneg_left velocityBound (pow_nonneg observerNonnegative 3)).trans
    (mul_le_mul_of_nonneg_right observerCube upperNonnegative)
  have algebra : (2 * distance) ^ 3 * upper = circulation / Real.pi *
      (640 * distance * neutral + 1280 * length * separation + 2048 * radius ^ 2) := by
    dsimp only [upper]
    field_simp
    ring
  rw [algebra] at scaled
  have distanceNeutral := mul_le_mul_of_nonneg_right distanceOne neutralNonnegative
  have bracketBound : 640 * distance * neutral + 1280 * length * separation + 2048 * radius ^ 2 ≤
      4096 * (neutral + length * separation + radius ^ 2) := by
    nlinarith only [distanceNeutral, neutralNonnegative, mul_nonneg lengthPositive.le separationNonnegative, sq_nonneg radius]
  have bracketNonnegative : 0 ≤ 640 * distance * neutral + 1280 * length * separation + 2048 * radius ^ 2 := by positivity
  have circulationBound : circulation / Real.pi ≤ circulation :=
    div_le_self circulationPositive.le (by linarith only [Real.pi_gt_three])
  apply scaled.trans
  apply (mul_le_mul_of_nonneg_right circulationBound bracketNonnegative).trans
  exact (mul_le_mul_of_nonneg_left bracketBound circulationPositive.le).trans_eq (by ring)

end EulerNonuniqueness.Paper.SourcePacketPhysicalGeometry
