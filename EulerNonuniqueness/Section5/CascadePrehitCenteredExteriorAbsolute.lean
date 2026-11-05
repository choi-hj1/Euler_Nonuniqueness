import EulerNonuniqueness.Section5.CascadePrehitCenteredExteriorReturn
import EulerNonuniqueness.Section5.CascadePrehitExternalDilationReturn

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_cascade_prehit_centered_exterior_absolute (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1 / 8) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count, index.val + 1 < count →
      ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
      (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
      ∀ time ∈ Icc 0 finish,
      ‖quadrupoleCenteredExternalIncrement {scales with frequency := frequency}
          prepared.trajectory.movingFamily.patchMotion index time‖ /
          ({scales with frequency := frequency} : Scales).length (index.val + 1) ≤
        42 * (96 / Real.pi * (2304 * ({scales with frequency := frequency} : Scales).strain)) := by
  filter_upwards [scales.eventually_cascade_prehit_centered_exterior_return amplitudePositive ratioBound alphaPositive
      orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_quadrupole_foreign_head_tail amplitudePositive ratioBound alphaPositive
      orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive (factorSmall.trans (by norm_num)),
    scales.eventually_cascade_prehit_centroid_extent amplitudePositive ratioBound alphaPositive
      (by linarith : 0 < scaleRoot) (by linarith : 0 ≤ boundaryConstant) thresholdSmall referenceNonnegative]
    with frequency fields coefficients extents
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let length := changed.length (index.val + 1)
  let radius := factor / 39321600 * changed.location (index.val + 1)
  let budget := 96 / Real.pi * (2304 * changed.strain)
  have lengthPositive : 0 < length := changed.length_pos _
  have fullInside : time ∈ Icc 0 path.stop := ⟨inside.1, inside.2.trans finishBound⟩
  have firstCoefficients := coefficients count phase dipoleAngle prepared path time fullInside index 0
  have secondCoefficients := coefficients count phase dipoleAngle prepared path time fullInside index 1
  change Summable (fun power => ‖quadrupoleExteriorCoefficient changed first index time radius power‖) ∧
    ‖quadrupoleExteriorCoefficient changed first index time radius 0‖ ≤ budget ∧
    (∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time radius (power + 1)‖) ≤ budget at firstCoefficients
  change Summable (fun power => ‖quadrupoleExteriorCoefficient changed second index time radius power‖) ∧
    ‖quadrupoleExteriorCoefficient changed second index time radius 0‖ ≤ budget ∧
    (∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed second index time radius (power + 1)‖) ≤ budget at secondCoefficients
  have budgetNonnegative : 0 ≤ budget := (norm_nonneg _).trans firstCoefficients.2.1
  have firstTotal : (∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time radius power‖) ≤ 2 * budget := by
    rw [firstCoefficients.1.tsum_eq_zero_add]
    linarith [firstCoefficients.2.1, firstCoefficients.2.2]
  have secondTotal : (∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed second index time radius power‖) ≤ 2 * budget := by
    rw [secondCoefficients.1.tsum_eq_zero_add]
    linarith [secondCoefficients.2.1, secondCoefficients.2.2]
  have differenceSummable : Summable (fun power : ℕ => ‖quadrupoleExteriorCoefficient changed first index time radius power -
      quadrupoleExteriorCoefficient changed second index time radius power‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_sub_le _ _) (firstCoefficients.1.add secondCoefficients.1)
  have differenceBound := differenceSummable.tsum_le_tsum (fun power => norm_sub_le
    (quadrupoleExteriorCoefficient changed first index time radius power)
    (quadrupoleExteriorCoefficient changed second index time radius power)) (firstCoefficients.1.add secondCoefficients.1)
  rw [firstCoefficients.1.tsum_add secondCoefficients.1] at differenceBound
  have differenceBudget : (∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time radius power -
      quadrupoleExteriorCoefficient changed second index time radius power‖) ≤ 4 * budget := by linarith
  have actualExtent := extents prepared path factorSmall index nonterminal finish finishNonnegative finishBound radialSmall time inside
  have firstExtent : ‖fun patch => patchCentroid first time index patch - quadrupoleCenter first time index‖ ≤ 3 * length :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun patch => (actualExtent patch).1
  have secondExtent : ‖fun patch => patchCentroid second time index patch - quadrupoleCenter second time index‖ ≤ 3 * length := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro patch
    simpa only [second, prepared.referenceIdentity] using (actualExtent patch).2
  have positionBound : ‖quadrupoleNormalizedCentroidOffsets first index time length -
      quadrupoleNormalizedCentroidOffsets second index time length‖ ≤ 6 := by
    rw [quadrupoleNormalizedCentroidOffsets_relative_norm_eq_div first second index time lengthPositive]
    apply (div_le_iff₀ lengthPositive).mpr
    exact (norm_sub_le _ _).trans (by linarith)
  have actual := fields count phase dipoleAngle prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  dsimp only at actual
  have relativeBound := actual.2.trans (add_le_add
    (mul_le_mul_of_nonneg_left positionBound (show 0 ≤ 4 * budget by positivity))
    (mul_le_mul_of_nonneg_left differenceBudget (by norm_num : (0 : ℝ) ≤ 3)))
  have triangle := norm_add_le
    (quadrupoleCenteredExternalIncrement changed first index time - quadrupoleCenteredExternalIncrement changed second index time)
    (quadrupoleCenteredExternalIncrement changed second index time)
  rw [sub_add_cancel] at triangle
  have divided := div_le_div_of_nonneg_right triangle lengthPositive.le
  rw [add_div] at divided
  exact (divided.trans (add_le_add relativeBound actual.1)).trans_eq (by ring)

end EulerNonuniqueness.Paper
