import EulerNonuniqueness.Section5.CascadeStoppedBoundaryGapFrequency
import EulerNonuniqueness.Section4.ReferenceBoundaryLabelGaps
import EulerNonuniqueness.Section3.FinitePatchRestriction

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

def cascadePairedMotion
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) : Fin 2 → PatchMotion count :=
  Fin.cases prepared.trajectory.movingFamily.patchMotion (fun _ => prepared.reference)

theorem Scales.eventually_cascade_paired_saddle_admissible (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {scaleRoot boundaryConstant factor threshold referenceConstant : ℝ}
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant) :
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {shapeRadius monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared,
    (∀ side, FinitePatchEvolution {scales with frequency := frequency} (cascadePairedMotion prepared side) path.stop) ∧
    (∀ source : Fin count, 0 < ({scales with frequency := frequency} : Scales).radius (source.val + 1)) ∧
    (∀ side, ∀ current ∈ Icc 0 path.stop, ∀ source patch,
      ∃ error ≤ (1 : ℝ), BoundaryCloseToCircle {scales with frequency := frequency}
        (cascadePairedMotion prepared side) current source patch error) ∧
    (∀ side, ∀ current ∈ Icc 0 path.stop, ∀ (source other : Fin count) (patch otherPatch : Fin 4),
      (other, otherPatch) ≠ (source, patch) →
      8 * ({scales with frequency := frequency} : Scales).radius (source.val + 1) +
        8 * ({scales with frequency := frequency} : Scales).radius (other.val + 1) <
        dist ((cascadePairedMotion prepared side).boundary current source patch 0)
          ((cascadePairedMotion prepared side).boundary current other otherPatch 0)) := by
  filter_upwards [eventually_ge_atTop (max 1 (referenceConstant + 1)),
    scales.eventually_stopped_cascade_boundary_label_gaps amplitudePositive ratioBound alphaPositive
      rootPositive boundaryNonnegative factorPositive factorSmall,
    scales.eventually_reference_coarse_boundary_label_gaps amplitudePositive ratioBound alphaPositive
      thresholdSmall referenceNonnegative]
    with frequency frequencyLarge actualGaps referenceGaps
  intro orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path
  let changed : Scales := {scales with frequency := frequency}
  have frequencyOne : 1 ≤ frequency := (le_max_left _ _).trans frequencyLarge
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith
  obtain ⟨unstable, phaseLift, initial, lift, referenceEvolution, referenceCoarse, sharp⟩ := prepared.referenceSolution
  have gaps := actualGaps prepared path
  have referenceInside {time : ℝ} (inside : time ∈ Icc 0 path.stop) : time ∈ Icc 0 (2 : ℝ) :=
    ⟨inside.1, by linarith [inside.2, path.stopBound]⟩
  refine ⟨?_, (fun source => changed.radius_pos amplitudePositive frequencyPositive ratioPositive _), ?_, ?_⟩
  · intro side
    fin_cases side
    · simpa only [cascadePairedMotion, Fin.cases_zero] using path.evolution
    · simpa only [cascadePairedMotion, Fin.cases_succ] using
        referenceEvolution.mono (show path.stop ≤ 2 by linarith [path.stopBound])
  · intro side current inside source patch
    fin_cases side
    · refine ⟨boundaryConstant / (scaleRoot ^ 2 * changed.omega (source.val + 1) ^ 2), gaps.1 source, ?_⟩
      simpa only [cascadePairedMotion, Fin.cases_zero] using path.boundary current inside source patch
    · have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (source.val + 1)
      have omegaBound := changed.omega_ge_frequency frequencyPositive (by dsimp only [changed]; linarith) (source.val + 1)
      have errorSmall : referenceConstant * (changed.omega (source.val + 1))⁻¹ ^ 2 ≤ 1 := by
        have one : 1 ≤ changed.omega (source.val + 1) := frequencyOne.trans omegaBound
        have constantBound : referenceConstant ≤ changed.omega (source.val + 1) := by
          have bound := (le_max_right 1 (referenceConstant + 1)).trans frequencyLarge
          linarith
        have numerator : referenceConstant ≤ changed.omega (source.val + 1) ^ 2 := by nlinarith
        have actual := (div_le_one (sq_pos_of_pos omegaPositive)).mpr numerator
        simpa only [div_eq_mul_inv, inv_pow] using actual
      refine ⟨_, errorSmall, ?_⟩
      simpa only [cascadePairedMotion, Fin.cases_succ] using
        (referenceCoarse.2.1 current (referenceInside inside) source).2.2.2.2.2 patch
  · intro side current inside source other patch otherPatch different
    fin_cases side
    · simpa only [cascadePairedMotion, Fin.cases_zero] using
        gaps.2 current inside source other patch otherPatch (Ne.symm different)
    · simpa only [cascadePairedMotion, Fin.cases_succ] using
        referenceGaps prepared.reference referenceCoarse current (referenceInside inside) source other patch otherPatch
          (Ne.symm different)

end EulerNonuniqueness.Paper
