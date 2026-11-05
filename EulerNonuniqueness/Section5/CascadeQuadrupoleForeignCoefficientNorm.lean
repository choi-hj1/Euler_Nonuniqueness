import EulerNonuniqueness.Section5.CascadeQuadrupoleForeignClearance
import EulerNonuniqueness.Section5.CascadeQuadrupoleMacroSupport
import EulerNonuniqueness.Section6.PaperRelativeNeutralPointSeries
import EulerNonuniqueness.Section6.MovingForeignQuadrupole
import EulerNonuniqueness.Section6.MovingExteriorWeightedNorm

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_cascade_quadrupole_foreign_coefficients_norm (scales : Scales)
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
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ time ∈ Icc 0 path.stop, ∀ receiver : Fin count,
      let changed : Scales := {scales with frequency := frequency}
      let radius := factor / 39321600 * changed.location (receiver.val + 1)
      let first := prepared.referenceWitness.trajectory.movingFamily.patchMotion
      let second := prepared.trajectory.movingFamily.patchMotion
      (∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖quadrupoleExteriorCoefficient changed first receiver time radius power‖) ≤
        96 / Real.pi * (2304 * changed.strain) ∧
      (∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖quadrupoleExteriorCoefficient changed second receiver time radius power‖) ≤
        96 / Real.pi * (2304 * changed.strain) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_cascade_quadrupole_foreign_clearance amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_quadrupole_macro_support amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall]
    with frequency frequencyBound clearance support
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let radius := factor / 39321600 * changed.location (receiver.val + 1)
  let distance := changed.location (receiver.val + 1) / 1000
  have locationPositive := changed.location_pos (receiver.val + 1)
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have distancePositive : 0 < distance := by dsimp only [distance]; positivity
  have ratioSmall : 96 * radius / distance ≤ 1 / 2 := by
    apply (div_le_iff₀ distancePositive).mpr
    dsimp only [radius, distance]
    nlinarith [mul_le_mul_of_nonneg_right factorSmall locationPositive.le]
  have actualClearance := clearance count phase dipoleAngle prepared path time inside receiver
  have actualSupport := support count phase dipoleAngle prepared path time inside receiver
  have referenceInside : time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, by linarith [inside.2, path.stopBound]⟩
  have referenceWeight := prepared.referenceWitness.trajectory.movingFamily.external_inverseSquare_weight_le_strain changed
    prepared.referenceWitness.evolution referenceInside prepared.referenceWitness.densityIdentity amplitudePositive
    frequencyBound ratioBound alphaPositive receiver _ actualClearance.1
  have alternativeWeight := prepared.trajectory.movingFamily.external_inverseSquare_weight_le_strain changed
    path.evolution inside prepared.densityIdentity amplitudePositive frequencyBound ratioBound alphaPositive receiver _ actualClearance.2
  constructor
  · have actual := Section6.tsum_exteriorVorticityCoefficient_half_weight_le
      (prepared.referenceWitness.evolution.externalPatchVorticity_integrable referenceInside receiver)
      (quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time receiver)
      radiusPositive.le distancePositive (by norm_num : (0 : ℝ) ≤ 96) actualSupport.1 ratioSmall
    exact actual.trans (mul_le_mul_of_nonneg_left referenceWeight (by positivity : 0 ≤ (96 : ℝ) / Real.pi))
  · have actual := Section6.tsum_exteriorVorticityCoefficient_half_weight_le
      (path.evolution.externalPatchVorticity_integrable inside receiver)
      (quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time receiver)
      radiusPositive.le distancePositive (by norm_num : (0 : ℝ) ≤ 96) actualSupport.2 ratioSmall
    exact actual.trans (mul_le_mul_of_nonneg_left alternativeWeight (by positivity : 0 ≤ (96 : ℝ) / Real.pi))

end EulerNonuniqueness.Paper
