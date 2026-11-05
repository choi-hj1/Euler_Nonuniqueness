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

private theorem zeroCoefficient_eq_velocity {count : ℕ}
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

theorem Scales.eventually_cascade_patch_external_velocity_continuous (scales : Scales)
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
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver : Fin count, ∀ patch : Fin 4,
      ContinuousOn (fun time =>
        biotSavart (externalPatchVorticity {scales with frequency := frequency}
          prepared.trajectory.movingFamily.patchMotion time receiver)
          (patchCentroid prepared.trajectory.movingFamily.patchMotion time receiver patch) -
        biotSavart (externalPatchVorticity {scales with frequency := frequency}
          prepared.referenceWitness.trajectory.movingFamily.patchMotion time receiver)
          (patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time receiver patch))
        (Icc 0 path.stop) := by
  filter_upwards [scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio)
      (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 1000)]
    with frequency alignment radii lengths
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver patch
  let changed : Scales := {scales with frequency := frequency}
  let distance := changed.location (receiver.val + 1) / 1000
  have distancePositive : 0 < distance := div_pos (changed.location_pos _) (by norm_num)
  have globalInside (time : ℝ) (inside : time ∈ Icc 0 path.stop) : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
  have radiusBound (source : Fin count) : changed.radius (source.val + 1) ≤ changed.location (source.val + 1) / 1000 := by
    have firstBound := (radii (source.val + 1)).le
    have secondBound := (lengths (source.val + 1)).le
    change changed.radius (source.val + 1) ≤ 1 * changed.length (source.val + 1) at firstBound
    change changed.length (source.val + 1) ≤ (1 / 1000 : ℝ) * changed.location (source.val + 1) at secondBound
    linarith only [firstBound, secondBound]
  have oneSide (family : FiniteMovingPatchFamily (count * 4))
      (inside : ∀ time ∈ Icc 0 path.stop, ∀ label,
        time ∈ Ioo (family.patch label).initialTime (family.patch label).finalTime)
      (densities : ∀ source sourcePatch, family.density (finProdFinEquiv (source, sourcePatch)) =
        patchSign sourcePatch * changed.amplitude * changed.omega (source.val + 1) ^ 4)
      (radiusIdentity : ∀ source sourcePatch,
        (family.patch (finProdFinEquiv (source, sourcePatch))).radius = changed.radius (source.val + 1))
      (centerIdentity : ∀ time ∈ Icc 0 path.stop, ∀ source sourcePatch,
        (family.patch (finProdFinEquiv (source, sourcePatch))).center time =
          patchCentroid family.patchMotion time source sourcePatch)
      (aligned : ∀ time ∈ Icc 0 path.stop, ∀ source, receiver ≠ source →
        ‖(patchCentroid family.patchMotion time receiver patch - quadrupoleCenter family.patchMotion time source) -
          ((changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ))‖ ≤
            3 * |changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 16)
      (extent : ∀ time ∈ Icc 0 path.stop, ∀ source, receiver ≠ source → ∀ sourcePatch,
        ‖patchCentroid family.patchMotion time source sourcePatch - quadrupoleCenter family.patchMotion time source‖ ≤
          changed.location (source.val + 1) / 100) :
      ContinuousOn (fun time => biotSavart (externalPatchVorticity changed family.patchMotion time receiver)
        (patchCentroid family.patchMotion time receiver patch)) (Icc 0 path.stop) := by
    have coefficients : ContinuousOn
        (family.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun time => patchCentroid family.patchMotion time receiver patch) 1 0) (Icc 0 path.stop) := by
      apply family.exteriorTaylorCoefficient_continuousOn_of_local_center_gaps
        (foreignQuadrupolePatchLabels receiver) _ 1 0 _ distancePositive
        (fun time member => family.patchCentroid_contDiffAt receiver patch (inside time member _))
        (fun time member source _ => inside time member source)
      intro time member label foreign
      obtain ⟨⟨source, sourcePatch⟩, rfl⟩ := finProdFinEquiv.surjective label
      have different : receiver ≠ source :=
        ((mem_foreignQuadrupolePatchLabels receiver source sourcePatch).mp foreign).symm
      rw [radiusIdentity, centerIdentity time member]
      have spacing := changed.location_sum_le_three_distance
        (show receiver.val + 1 ≠ source.val + 1 from fun equality =>
          different (Fin.ext (Nat.add_right_cancel equality)))
      have normIdeal : ‖(changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)‖ =
          |changed.location (receiver.val + 1) - changed.location (source.val + 1)| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have first := norm_sub_norm_le
        ((changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ))
        (patchCentroid family.patchMotion time receiver patch - quadrupoleCenter family.patchMotion time source)
      rw [normIdeal, norm_sub_rev ((changed.location (receiver.val + 1) : ℂ) -
        (changed.location (source.val + 1) : ℂ))] at first
      have second := norm_sub_norm_le
        (patchCentroid family.patchMotion time receiver patch - quadrupoleCenter family.patchMotion time source)
        (patchCentroid family.patchMotion time source sourcePatch - quadrupoleCenter family.patchMotion time source)
      rw [sub_sub_sub_cancel_right] at second
      dsimp only [distance]
      linarith only [first, second, spacing, radiusBound source, aligned time member source different,
        extent time member source different sourcePatch,
        changed.location_pos (receiver.val + 1), changed.location_pos (source.val + 1)]
    apply coefficients.congr
    intro time member
    dsimp only
    rw [zeroCoefficient_eq_velocity, family.externalPatchVorticity_eq_subfamily changed densities]
  have first := oneSide prepared.trajectory.movingFamily
    (fun time member _ => globalInside time member) prepared.densityIdentity prepared.radiusIdentity
    (fun time member source sourcePatch =>
      prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) (globalInside time member) source sourcePatch)
    (fun time member source different =>
      (alignment count phase dipoleAngle prepared path time member (receiver, patch) source different).2.1)
    (fun time member source different =>
      (alignment count phase dipoleAngle prepared path time member (receiver, patch) source different).2.2.2)
  have second := oneSide prepared.referenceWitness.trajectory.movingFamily
    (fun time member _ => globalInside time member) prepared.referenceWitness.densityIdentity prepared.referenceWitness.radiusIdentity
    (fun time member source sourcePatch =>
      prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) (globalInside time member) source sourcePatch)
    (fun time member source different =>
      (alignment count phase dipoleAngle prepared path time member (receiver, patch) source different).1)
    (fun time member source different =>
      (alignment count phase dipoleAngle prepared path time member (receiver, patch) source different).2.2.1)
  exact first.sub second

end EulerNonuniqueness.Paper

