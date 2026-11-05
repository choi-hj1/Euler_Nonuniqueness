import EulerNonuniqueness.Section5.CascadeIndividualSourcePatchCoefficientContinuity
import EulerNonuniqueness.Section6.MovingExteriorContourSeries
import EulerNonuniqueness.Section6.MovingForeignQuadrupole

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

private theorem source_zeroCoefficient_eq_velocity {count : ℕ}
    (family : FiniteMovingPatchFamily count) (selected : Finset (Fin count))
    (center : ℝ → ℂ) (time : ℝ) :
    family.exteriorTaylorCoefficient selected center 1 0 time =
      biotSavart (family.subfamilyVorticity selected time) (center time) := by
  rw [family.biotSavart_subfamily_eq_sum]
  simp only [FiniteMovingPatchFamily.exteriorTaylorCoefficient, pow_zero, one_mul,
    Nat.zero_sub, Nat.zero_add, pow_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro source member
  unfold FiniteMovingPatchFamily.patchVorticity
  rw [Section6.biotSavart_indicator_density_integral
    ((family.patch source).domain_isOpen time).measurableSet]
  simp_rw [biotSavartKernel_eq_conj_inv]
  rw [integral_const_mul]
  simp only [Complex.real_smul, Complex.star_def]
  ring

private theorem source_subfamily_density_identity {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityIdentity : ∀ index patch, family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (source : Fin count) (time : ℝ) :
    (family.quadrupoleSubfamily source).subfamilyVorticity Finset.univ time =
      quadrupoleDensity scales family.patchMotion time source := by
  funext position
  change (∑ patch : Fin 4, family.patchVorticity time (finProdFinEquiv (source, patch)) position) = _
  unfold quadrupoleDensity
  apply Finset.sum_congr rfl
  intro patch member
  exact congrFun (family.patchDensity_eq scales densityIdentity time source patch).symm position

theorem Scales.eventually_cascade_individual_source_velocity_continuous (scales : Scales)
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
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver : Fin count × Fin 4, ∀ source : Fin count,
      receiver.1 ≠ source →
      ContinuousOn (fun time =>
        biotSavart (quadrupoleDensity {scales with frequency := frequency}
          prepared.trajectory.movingFamily.patchMotion time source)
          (patchCentroid prepared.trajectory.movingFamily.patchMotion time receiver.1 receiver.2) -
        biotSavart (quadrupoleDensity {scales with frequency := frequency}
          prepared.referenceWitness.trajectory.movingFamily.patchMotion time source)
          (patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time receiver.1 receiver.2))
        (Icc 0 path.stop) := by
  filter_upwards [scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 1000)]
    with frequency alignment radii lengths
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source different
  let changed : Scales := {scales with frequency := frequency}
  let gap := |changed.location (receiver.1.val + 1) - changed.location (source.val + 1)|
  let ideal : ℂ := (changed.location (receiver.1.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
  have gapPositive : 0 < gap := changed.location_distance_pos
    (fun equality => different (Fin.ext (Nat.add_right_cancel equality)))
  have idealNorm : ‖ideal‖ = gap := by
    dsimp only [ideal, gap]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have radiusSmall : changed.radius (source.val + 1) ≤ changed.location (source.val + 1) / 1000 := by
    have first := (radii (source.val + 1)).le
    have second := (lengths (source.val + 1)).le
    change changed.radius (source.val + 1) ≤ 1 * changed.length (source.val + 1) at first
    change changed.length (source.val + 1) ≤ (1 / 1000 : ℝ) * changed.location (source.val + 1) at second
    linarith
  have globalInside (time : ℝ) (inside : time ∈ Icc 0 path.stop) : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have spacing := changed.location_sum_le_three_distance
    (show receiver.1.val + 1 ≠ source.val + 1 from fun equality => different (Fin.ext (Nat.add_right_cancel equality)))
  have oneFamily (family : FiniteMovingPatchFamily (count * 4))
      (inside : ∀ time ∈ Icc 0 path.stop, ∀ label, time ∈ Ioo (family.patch label).initialTime (family.patch label).finalTime)
      (radiusIdentity : ∀ patch, (family.patch (finProdFinEquiv (source, patch))).radius = changed.radius (source.val + 1))
      (centerIdentity : ∀ time ∈ Icc 0 path.stop, ∀ patch,
        (family.patch (finProdFinEquiv (source, patch))).center time = patchCentroid family.patchMotion time source patch)
      (aligned : ∀ time ∈ Icc 0 path.stop,
        ‖(patchCentroid family.patchMotion time receiver.1 receiver.2 - quadrupoleCenter family.patchMotion time source) - ideal‖ ≤ 3 * gap / 16)
      (extent : ∀ time ∈ Icc 0 path.stop, ∀ patch,
        ‖patchCentroid family.patchMotion time source patch - quadrupoleCenter family.patchMotion time source‖ ≤ changed.location (source.val + 1) / 100) :
      ContinuousOn ((family.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
        (fun time => patchCentroid family.patchMotion time receiver.1 receiver.2) 1 0) (Icc 0 path.stop) := by
    apply (family.quadrupoleSubfamily source).exteriorTaylorCoefficient_continuousOn_of_local_center_gaps
      Finset.univ _ 1 0 _ (div_pos gapPositive (by norm_num : (0 : ℝ) < 8))
      (fun time member => family.patchCentroid_contDiffAt receiver.1 receiver.2 (inside time member _))
      (fun time member patch _ => inside time member (finProdFinEquiv (source, patch)))
    intro time member patch _
    change gap / 8 + 3 * (family.patch (finProdFinEquiv (source, patch))).radius ≤
      ‖patchCentroid family.patchMotion time receiver.1 receiver.2 -
        (family.patch (finProdFinEquiv (source, patch))).center time‖
    rw [radiusIdentity, centerIdentity time member]
    have first := norm_sub_norm_le ideal
      (patchCentroid family.patchMotion time receiver.1 receiver.2 - quadrupoleCenter family.patchMotion time source)
    rw [idealNorm, norm_sub_rev ideal] at first
    have second := norm_sub_norm_le
      (patchCentroid family.patchMotion time receiver.1 receiver.2 - quadrupoleCenter family.patchMotion time source)
      (patchCentroid family.patchMotion time source patch - quadrupoleCenter family.patchMotion time source)
    rw [sub_sub_sub_cancel_right] at second
    linarith [aligned time member, extent time member patch, changed.location_pos (receiver.1.val + 1)]
  have first := oneFamily prepared.trajectory.movingFamily (fun time member _ => globalInside time member)
    (prepared.radiusIdentity source)
    (fun time member patch => prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) (globalInside time member) source patch)
    (fun time member => (alignment count phase dipoleAngle prepared path time member receiver source different).2.1)
    (fun time member => (alignment count phase dipoleAngle prepared path time member receiver source different).2.2.2)
  have second := oneFamily prepared.referenceWitness.trajectory.movingFamily (fun time member _ => globalInside time member)
    (prepared.referenceWitness.radiusIdentity source)
    (fun time member patch => prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) (globalInside time member) source patch)
    (fun time member => (alignment count phase dipoleAngle prepared path time member receiver source different).1)
    (fun time member => (alignment count phase dipoleAngle prepared path time member receiver source different).2.2.1)
  apply (first.sub second).congr
  intro time member
  dsimp only
  rw [source_zeroCoefficient_eq_velocity, source_zeroCoefficient_eq_velocity,
    source_subfamily_density_identity prepared.trajectory.movingFamily changed prepared.densityIdentity,
    source_subfamily_density_identity prepared.referenceWitness.trajectory.movingFamily changed prepared.referenceWitness.densityIdentity]

end EulerNonuniqueness.Paper

