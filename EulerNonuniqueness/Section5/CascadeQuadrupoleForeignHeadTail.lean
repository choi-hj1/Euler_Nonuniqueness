import EulerNonuniqueness.Section5.CascadeQuadrupoleForeignCoefficientNorm
import EulerNonuniqueness.Section5.CascadeRelativeNeutralHistory
import EulerNonuniqueness.Section6.ExteriorCoefficientHeadTail

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_cascade_quadrupole_foreign_head_tail (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ time ∈ Icc 0 path.stop, ∀ receiver : Fin count, ∀ side : Fin 2,
      let changed : Scales := {scales with frequency := frequency}
      let radius := factor / 39321600 * changed.location (receiver.val + 1)
      let coefficient := quadrupoleExteriorCoefficient changed (cascadePairedMotion prepared side) receiver time radius
      Summable (fun power => ‖coefficient power‖) ∧
      ‖coefficient 0‖ ≤ 96 / Real.pi * (2304 * changed.strain) ∧
      (∑' power : ℕ, ‖coefficient (power + 1)‖) ≤ 96 / Real.pi * (2304 * changed.strain) := by
  filter_upwards [scales.eventually_cascade_quadrupole_foreign_coefficients_norm amplitudePositive ratioBound alphaPositive
      orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_quadrupole_macro_support amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall] with frequency coefficientBound support
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver side
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let radius := factor / 39321600 * changed.location (receiver.val + 1)
  let distance := changed.location (receiver.val + 1) / 1000
  have locationPositive := changed.location_pos (receiver.val + 1)
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have distancePositive : 0 < distance := by dsimp only [distance]; positivity
  have ratioSmall : 96 * radius / distance < 1 := by
    apply (div_lt_one distancePositive).mpr
    dsimp only [radius, distance]
    nlinarith [mul_le_mul_of_nonneg_right factorSmall locationPositive.le]
  have actualSupport := support count phase dipoleAngle prepared path time inside receiver
  have actualBound := coefficientBound count phase dipoleAngle prepared path time inside receiver
  have oneSide (motion : PatchMotion count) (evolution : FinitePatchEvolution changed motion path.stop)
      (separated : ∀ source ∈ Function.support (externalPatchVorticity changed motion time receiver),
        distance ≤ ‖quadrupoleCenter motion time receiver - source‖)
      (bounded : (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖quadrupoleExteriorCoefficient changed motion receiver time radius power‖) ≤ 96 / Real.pi * (2304 * changed.strain)) :
      Summable (fun power => ‖quadrupoleExteriorCoefficient changed motion receiver time radius power‖) ∧
      ‖quadrupoleExteriorCoefficient changed motion receiver time radius 0‖ ≤ 96 / Real.pi * (2304 * changed.strain) ∧
      (∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed motion receiver time radius (power + 1)‖) ≤
        96 / Real.pi * (2304 * changed.strain) := by
    have weighted := Section6.summable_exteriorVorticityCoefficient_weight
      (evolution.externalPatchVorticity_integrable inside receiver) (quadrupoleCenter motion time receiver)
      radiusPositive.le distancePositive (by norm_num : (0 : ℝ) ≤ 96) separated ratioSmall
    have estimates := Section6.coefficient_norm_head_tail_le_weighted_tsum
      (quadrupoleExteriorCoefficient changed motion receiver time radius) (by norm_num : (1 : ℝ) ≤ 96) weighted
    refine ⟨?_, estimates.1.trans bounded, estimates.2.trans bounded⟩
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun power =>
      le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 96))) weighted
  fin_cases side
  · exact oneSide _ path.evolution actualSupport.2 actualBound.2
  · simp only [cascadePairedMotion, Fin.cases_succ, prepared.referenceIdentity]
    exact oneSide _ (prepared.referenceWitness.evolution.mono (show path.stop ≤ 2 by linarith [path.stopBound]))
      actualSupport.1 actualBound.1

end EulerNonuniqueness.Paper
