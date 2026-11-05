import EulerNonuniqueness.Section6.SourcePacketInheritedMomentArbitraryBudget
import EulerNonuniqueness.Section5.CascadePostHitScalarBudget
import EulerNonuniqueness.Section5.CascadeInternallyStoppedPath
import EulerNonuniqueness.Section7.PaperDipoleDynamics

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000

theorem Scales.eventually_actual_inherited_moment_arbitrary_budget (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {factor threshold scaleRoot boundaryConstant tolerance : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) (rootPositive : 0 < scaleRoot)
    (boundaryNonnegative : 0 ≤ boundaryConstant) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count,
    ∀ start ∈ Icc 0 path.stop, ∀ outgoingRadius : ℝ, 32 ≤ outgoingRadius →
    12 * outgoingRadius ≤ tolerance * scales.ratio → ∀ direction displacement : ℂ,
    ‖direction‖ = 1 → displacement ≠ 0 →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let length : ℝ := changed.length (index.val + 1)
    ‖firstDipoleSeparation motion start index - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation motion start index - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    ‖firstDipoleCenter motion start index - secondDipoleCenter motion start index‖ ≤
      (5 / 4 : ℝ) * length * outgoingRadius →
    let moment := ∫ position, quadrupoleDensity changed motion start index position •
      (position - quadrupoleCenter motion start index) ^ 2
    6 * ‖moment‖ / (Real.pi * ‖displacement‖ ^ 4 * (2 * Real.sqrt 2 * changed.omega index.val)) ≤
      tolerance * (Real.sqrt 3 * changed.circulation (index.val + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega index.val ^ 2 * ‖displacement‖ ^ 4)) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_cascade_posthit_scalar_budgets amplitudePositive ratioBound alphaPositive factorPositive
      rootPositive boundaryNonnegative (by norm_num : (0 : ℝ) < 1),
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      factorPositive factorSmall (by norm_num : (3 : ℝ) ≤ 3)]
    with frequency frequencyOne budgets geometry
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path index start inside outgoingRadius
    outgoingRadiusLarge ratioBudget direction displacement directionNorm displacementNonzero
  dsimp only
  intro firstInitial secondInitial centerBound
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have lengthPositive := changed.length_pos (index.val + 1)
  have configuration : relabelNegativePoints (fun patch => patchCentroid motion start index patch) =
      twoDipoleConfiguration (firstDipoleCenter motion start index) (secondDipoleCenter motion start index)
        (firstDipoleSeparation motion start index) (secondDipoleSeparation motion start index) := by
    funext patch
    rw [twoDipoleConfiguration_patchCentroids]
    fin_cases patch <;> rfl
  have firstBound := (dipole_separation_norm_bounds _ lengthPositive directionNorm
    (firstInitial.trans (by linarith : changed.length (index.val + 1) / 64 ≤ changed.length (index.val + 1) / 16))).2
  have secondBound := (dipole_separation_norm_bounds _ lengthPositive
    (show ‖-direction‖ = 1 by simpa using directionNorm)
    (secondInitial.trans (by linarith : changed.length (index.val + 1) / 64 ≤ changed.length (index.val + 1) / 16))).2
  have radiusSmall : changed.radius (index.val + 1) ≤ changed.length (index.val + 1) := by
    have first := (geometry (index.val + 1)).2.1
    have second := mul_le_of_le_one_left lengthPositive.le factorSmall
    linarith
  have momentBound := path.evolution.quadrupole_outgoing_initial_moment_bound inside amplitudePositive frequencyPositive
    ratioPositive index (firstDipoleCenter motion start index) (secondDipoleCenter motion start index)
    (firstDipoleSeparation motion start index) (secondDipoleSeparation motion start index) configuration
    (path.boundary start inside index) (by positivity) (budgets.2 count index).1
    (by linarith : 0 ≤ outgoingRadius) centerBound firstBound secondBound
  exact changed.initial_moment_weighted_arbitrary_cost index.val frequencyPositive ratioPositive
    (norm_pos_iff.mpr displacementNonzero) outgoingRadiusLarge tolerancePositive ratioBudget radiusSmall
    (by positivity) (budgets.2 count index).1 _ momentBound

end EulerNonuniqueness.Paper
