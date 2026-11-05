import EulerNonuniqueness.Section5.CascadeForeignVirtualReceiverRadius
import EulerNonuniqueness.Section6.ForeignExteriorScaledWeight
import EulerNonuniqueness.Section6.MovingExteriorWeightedNorm

noncomputable section

open Set Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem Scales.eventually_cascade_reference_foreign_coefficients_norm (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {threshold referenceConstant factor : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ phase dipoleAngle : ℕ → ℝ, ∀ {scaleRoot shapeRadius monitor boundaryConstant : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ time ∈ Icc 0 path.stop,
      ∀ receiver : Fin count × Fin 4,
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.referenceWitness.trajectory.movingFamily
      let virtualRadius := factor / 39321600 * changed.location (receiver.1.val + 1)
      (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
          (first.patch (finProdFinEquiv receiver)).center virtualRadius (power + 1) time‖) ≤
        96 / Real.pi * (2304 * changed.strain / (factor / 8) ^ 2) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_cascade_foreign_virtual_receiver_radius amplitudePositive ratioBound alphaPositive
      thresholdSmall referenceNonnegative factorPositive factorSmall,
    scales.eventually_actual_cascade_source_comparison_geometry amplitudePositive ratioBound alphaPositive
      thresholdSmall referenceNonnegative factorPositive factorSmall (weight := 1) (by norm_num)
      (parameterRadius := 1) (by norm_num)] with frequency frequencyBound virtualGeometry geometry
  intro count orbit sectionTime phase dipoleAngle scaleRoot shapeRadius monitor boundaryConstant
    prepared path time inside receiver
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.referenceWitness.trajectory.movingFamily
  let selected := foreignQuadrupolePatchLabels receiver.1
  let virtualRadius := factor / 39321600 * changed.location (receiver.1.val + 1)
  let distance := factor / 1600 * changed.location (receiver.1.val + 1)
  have actualGeometry := virtualGeometry count orbit sectionTime phase dipoleAngle prepared path time inside receiver
  have individualSeparated (label : Fin (count * 4)) (member : label ∈ selected)
      (position : ℂ) (sourceInside : position ∈ (first.patch label).domain time) :
      (factor / 8) * (|changed.location (receiver.1.val + 1) -
        changed.location ((finProdFinEquiv.symm label).1.val + 1)| / 8) ≤
        ‖(first.patch (finProdFinEquiv receiver)).center time - position‖ := by
    let source := finProdFinEquiv.symm label
    have sourceIdentity : finProdFinEquiv source = label := finProdFinEquiv.apply_symm_apply label
    have sourceDifferent : source.1 ≠ receiver.1 := by
      apply (mem_foreignQuadrupolePatchLabels receiver.1 source.1 source.2).mp
      simpa only [sourceIdentity] using member
    have different : receiver ≠ source := fun equality => sourceDifferent (congrArg Prod.fst equality.symm)
    have indexDifferent : source.1.val + 1 ≠ receiver.1.val + 1 :=
      fun equality => sourceDifferent (Fin.ext (Nat.add_right_cancel equality))
    have lower := (geometry count orbit sectionTime phase dipoleAngle prepared path time inside receiver source different).2.1
    change 2 * (first.patch (finProdFinEquiv source)).radius +
      (factor / 8) * changed.individualInteractionDistance (receiver.1.val + 1) (source.1.val + 1) ≤
      ‖(first.patch (finProdFinEquiv receiver)).center time - (first.patch (finProdFinEquiv source)).center time‖ at lower
    rw [Scales.individualInteractionDistance, if_neg indexDifferent, sourceIdentity] at lower
    have sourceBound := (Metric.mem_ball.mp ((first.patch label).domain_subset_ball time sourceInside)).le
    rw [dist_eq_norm] at sourceBound
    have triangle := norm_add_le ((first.patch (finProdFinEquiv receiver)).center time - position)
      (position - (first.patch label).center time)
    rw [sub_add_sub_cancel] at triangle
    linarith
  have referenceInside : time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, by linarith [inside.2, path.stopBound]⟩
  have weightBound := first.external_inverseSquare_weight_le_scaled_strain changed
    prepared.referenceWitness.evolution referenceInside prepared.referenceWitness.densityIdentity
    amplitudePositive frequencyBound ratioBound alphaPositive (show 0 < factor / 8 by positivity)
    receiver.1 ((first.patch (finProdFinEquiv receiver)).center time) individualSeparated
  have ratioSmall : 96 * virtualRadius / distance ≤ 1 / 2 := by
    apply (div_le_iff₀ actualGeometry.2.1).mpr
    dsimp only [virtualRadius, distance]
    nlinarith [mul_pos factorPositive (changed.location_pos (receiver.1.val + 1))]
  have actual := first.tsum_exteriorTaylorCoefficient_weight_le selected
    (first.patch (finProdFinEquiv receiver)).center virtualRadius time actualGeometry.1.le
    actualGeometry.2.1 (by norm_num : (0 : ℝ) ≤ 96) actualGeometry.2.2.2.2.1 ratioSmall
  exact actual.trans (mul_le_mul_of_nonneg_left weightBound (by positivity : 0 ≤ (96 : ℝ) / Real.pi))

end EulerNonuniqueness.Paper
