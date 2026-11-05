import EulerNonuniqueness.Section5.CascadeNormalizedPointEquation
import EulerNonuniqueness.Section5.CascadeCenteredForcingBound
import EulerNonuniqueness.Section6.CenteredPointNormScaling

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem Scales.eventually_material_normalized_point_forcing_bound (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {factor threshold scaleRoot boundaryConstant : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count,
    ∀ start time : ℝ, ∀ rotation : ℂ, ‖rotation‖ = 1 →
    start + time / ({scales with frequency := frequency} : Scales).omega (index.val + 1) ∈ Icc 0 path.stop →
      ‖cascadeNormalizedPointForcing {scales with frequency := frequency}
          prepared.trajectory.movingFamily.patchMotion index start rotation time‖ ≤
        (1 / (2048 * ({scales with frequency := frequency} : Scales).omega (index.val + 1))) *
          (‖cascadeNormalizedPointPositions {scales with frequency := frequency}
            prepared.trajectory.movingFamily.patchMotion index start rotation time‖ + 1) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_material_centered_forcing_bound amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorSmall rootPositive boundaryNonnegative] with frequency frequencyOne bounds
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path index start time rotation rotationNorm inside
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have bound := bounds count phase dipoleAngle prepared path index
    (start + time / changed.omega (index.val + 1)) inside
  have actual := normalized_forcing_bound_of_centered_bound
    (frequency := changed.omega (index.val + 1))
    (changed.omega_pos frequencyPositive ratioPositive (index.val + 1)) (changed.length_pos (index.val + 1)) rotationNorm bound
  change ‖cascadeNormalizedPointForcing changed prepared.trajectory.movingFamily.patchMotion index start rotation time‖ ≤
    ((1 / 2048 : ℝ) / changed.omega (index.val + 1)) *
      (‖cascadeNormalizedPointPositions changed prepared.trajectory.movingFamily.patchMotion index start rotation time‖ + 1) at actual
  have scalar (omega : ℝ) : (1 / 2048 : ℝ) / omega = 1 / (2048 * omega) := by ring
  rw [scalar] at actual
  exact actual

end EulerNonuniqueness.Paper
