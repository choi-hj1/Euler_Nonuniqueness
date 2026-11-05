import EulerNonuniqueness.Section5.CascadeActualQuadrupoleComparison
import EulerNonuniqueness.Section5.CascadeForeignReceiverAlignment
import EulerNonuniqueness.Section6.MacroFollowerGeometry

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem CascadeSourcePreparedPair.sourceComparison_quadrupole_mass_budget
    {rawCap sourceRadius : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
    {phase dipoleAngle : ℕ → ℝ} {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ}
    {count : ℕ}
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (receiver : Fin (count * 4))
    (shapes : ∀ label, ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
      ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label))
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (source : Fin count) (patch : Fin 4) :
    let comparison := (prepared.sourceComparison path inside receiver shapes).quadrupole source
    |(comparison.source patch).density| * (comparison.source patch).first.radius ^ 2 ≤ scales.circulation (source.val + 1) := by
  let comparison := (prepared.sourceComparison path inside receiver shapes).quadrupole source
  have mass := prepared.sourceComparison_quadrupole_masses path inside receiver shapes amplitudePositive frequencyPositive ratioPositive source patch
  change comparison.first.density patch * MeasureTheory.volume.real ((comparison.first.patch patch).domain comparison.time) =
    scales.circulation (source.val + 1) * Section6.fourPointSign patch at mass
  rw [comparison.firstArea patch] at mass
  have signAbs : |Section6.fourPointSign patch| = 1 := by
    by_cases positive : patch.val < 2 <;> simp [Section6.fourPointSign, positive]
  exact signed_circle_mass_budget (scales.circulation_pos frequencyPositive ratioPositive _).le signAbs mass

theorem Scales.eventually_cascade_macro_follower_centroid_clearance (scales : Scales)
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
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ time ∈ Icc 0 path.stop,
      ∀ receiver source : Fin count, receiver ≠ source → ∀ patch : Fin 4,
      let changed : Scales := {scales with frequency := frequency}
      let motion := prepared.trajectory.movingFamily.patchMotion
      |changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 8 ≤
        ‖quadrupoleCenter motion time receiver - patchCentroid motion time source patch‖ := by
  filter_upwards [scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall] with frequency alignment
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver source different patch
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let frozen : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
  let gap := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
  have aligned := (alignment count phase dipoleAngle prepared path time inside (receiver, 0) source different).2.1
  have geometry := changed.location_sum_le_three_distance
    (show receiver.val + 1 ≠ source.val + 1 from fun equality => different (Fin.ext (Nat.add_right_cancel equality)))
  exact macro_follower_centroid_clearance (abs_nonneg _) (by
      dsimp only [frozen, gap]; rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs])
    geometry aligned (path.centroid_extent inside receiver 0).le (path.centroid_extent inside source patch).le

end EulerNonuniqueness.Paper
