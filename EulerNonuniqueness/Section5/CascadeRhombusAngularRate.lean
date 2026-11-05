import EulerNonuniqueness.Section5.CascadeRhombusOwnGeometry
import EulerNonuniqueness.Section5.CascadeRhombusForeignGeometry
import EulerNonuniqueness.Section4.ReferenceClosedAngularFlux
import EulerNonuniqueness.Section1.ForeignInteractionWeight

noncomputable section

open Set Metric
open scoped NNReal

namespace EulerNonuniqueness.Paper.CascadeInternallyStoppedPath

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
  {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
    scaleRoot shapeRadius factor monitor boundaryConstant count}

set_option maxHeartbeats 2000000

theorem rhombus_internal_domain_gap (path : CascadeInternallyStoppedPath prepared)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop) (index : Fin count)
    (differenceLower : scales.length (index.val + 1) ^ 2 / 2 ≤
      diagonalDifference prepared.trajectory.movingFamily.patchMotion time index)
    (radialSmall : |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2)
    (asymmetrySmall : ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index‖ ≤
      scales.length (index.val + 1) / 64)
    (radiusSmall : scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000)
    (receiver source : Fin 4) (different : source ≠ receiver)
    {position location : ℂ}
    (positionInside : position ∈ prepared.trajectory.movingFamily.patchMotion.domain time index receiver)
    (locationInside : location ∈ prepared.trajectory.movingFamily.patchMotion.domain time index source) :
    scales.length (index.val + 1) / 200 ≤ ‖position - location‖ := by
  have lengthPositive := scales.length_pos (index.val + 1)
  have gap := patchCentroid_pair_strict_eighth_of_rhombus_shape
    prepared.trajectory.movingFamily.patchMotion time index lengthPositive differenceLower radialSmall asymmetrySmall
    receiver source different.symm
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have firstBound := prepared.trajectory.domain_subset_centroid_ball scales prepared.radiusIdentity
    (fun _ => rfl) globalInside index receiver positionInside
  have secondBound := prepared.trajectory.domain_subset_centroid_ball scales prepared.radiusIdentity
    (fun _ => rfl) globalInside index source locationInside
  simp only [mem_closedBall, dist_eq_norm] at firstBound secondBound
  have first := norm_sub_le_norm_sub_add_norm_sub
    (patchCentroid prepared.trajectory.movingFamily.patchMotion time index receiver) position
    (patchCentroid prepared.trajectory.movingFamily.patchMotion time index source)
  rw [norm_sub_rev (patchCentroid prepared.trajectory.movingFamily.patchMotion time index receiver) position] at first
  have second := norm_sub_le_norm_sub_add_norm_sub position location
    (patchCentroid prepared.trajectory.movingFamily.patchMotion time index source)
  linarith

theorem rhombus_angularImpulse_deriv_scale_bound (path : CascadeInternallyStoppedPath prepared)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (factorSmall : factor ≤ 1 / 8) {time : ℝ} (inside : time ∈ Icc 0 path.stop)
    (index : Fin count)
    (differenceLower : scales.length (index.val + 1) ^ 2 / 2 ≤
      diagonalDifference prepared.trajectory.movingFamily.patchMotion time index)
    (differenceUpper : diagonalDifference prepared.trajectory.movingFamily.patchMotion time index ≤
      2 * scales.length (index.val + 1) ^ 2)
    (radialSmall : |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2)
    (asymmetrySmall : ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index‖ ≤
      scales.length (index.val + 1) / 64)
    (lengthSmall : scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (radiusSmall : scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000)
    (radiusLocation : ∀ source : Fin count, scales.radius (source.val + 1) ≤ scales.location (source.val + 1) / 1000)
    {memory : ℝ} (memoryNonnegative : 0 ≤ memory)
    (asymmetryBound : ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index‖ ≤
      memory * scales.hessian * scales.length (index.val + 1) ^ 2)
    (omegaLength : scales.omega (index.val + 1) * scales.length (index.val + 1) ≤ 1)
    (hessianBound : scales.hessian ≤ 1) :
    |deriv (fun current => angularImpulse scales prepared.trajectory.movingFamily.patchMotion current index) time| ≤
      (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) *
        (2400 * memory * scales.hessian + (12 * memory + 36) * (1152 / Real.pi) * scales.strain) := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have lengthPositive := scales.length_pos (index.val + 1)
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ scales.hessian := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (scales.location_pos _).le _)
  let strain : ℝ≥0 := ⟨(1152 / Real.pi) * scales.strain, by positivity⟩
  let distance := fun source : Fin count =>
    |scales.location (index.val + 1) - scales.location (source.val + 1)| / 8
  have own := path.rhombus_own_domain_geometry inside index differenceLower differenceUpper radialSmall
    asymmetrySmall radiusSmall factorSmall
  have foreign (source : Fin count) (member : source ∈ Finset.univ.erase index) :=
    path.rhombus_ball_foreign_geometry inside index lengthSmall radiusLocation source (Finset.mem_erase.mp member).1
  have positive (source : Fin count) (member : source ∈ Finset.univ.erase index) : 0 < distance source :=
    div_pos (scales.location_distance_pos (fun equality =>
      (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equality).symm))) (by norm_num)
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have material (label : Fin (count * 4)) (angle : ℝ) := path.material_boundary inside label angle
  rw [prepared.trajectory.movingFamily.patchVorticity_eq scales prepared.densityIdentity] at material
  have estimate := prepared.trajectory.movingFamily.quadrupole_angularImpulse_deriv_closed_bound
    (strain := strain) scales prepared.densityIdentity path.evolution inside amplitudePositive frequencyPositive ratioPositive
    (fun _ => globalInside) material index (by positivity : 0 ≤ 3 * scales.length (index.val + 1))
    (by positivity : 0 < scales.length (index.val + 1) / 200) own.2
    (fun receiver source different position positionInside location locationInside =>
      path.rhombus_internal_domain_gap inside index differenceLower radialSmall asymmetrySmall radiusSmall
        receiver source different positionInside locationInside)
    distance positive (fun position positionInside source sourceMember => (foreign source sourceMember).2 position positionInside)
    (scales.foreign_strain_weight_le frequencyBound ratioBound alphaPositive index)
  have velocityIdentity : 3 * (scales.circulation (index.val + 1) /
      (2 * Real.pi * (scales.length (index.val + 1) / 200))) =
      600 * scales.omega (index.val + 1) * scales.length (index.val + 1) := by
    rw [Scales.circulation]
    field_simp
    <;> ring
  rw [velocityIdentity] at estimate
  have firstCost := mul_le_mul_of_nonneg_left omegaLength
    (by positivity : 0 ≤ 2400 * memory * scales.hessian)
  have lengthBound := scales.length_le_one frequencyPositive ratioPositive (index.val + 1)
  have productSmall : scales.hessian * scales.length (index.val + 1) ≤ 1 :=
    (mul_le_mul hessianBound lengthBound lengthPositive.le (by norm_num)).trans_eq (by ring)
  have middleCost : 12 * memory * scales.hessian * (strain : ℝ) * scales.length (index.val + 1) ≤
      12 * memory * (strain : ℝ) := by
    calc
      _ = (12 * memory * (strain : ℝ)) * (scales.hessian * scales.length (index.val + 1)) := by ring
      _ ≤ (12 * memory * (strain : ℝ)) * 1 := mul_le_mul_of_nonneg_left productSmall (by positivity)
      _ = _ := by ring
  apply estimate.trans
  calc
    _ ≤ 8 * scales.circulation (index.val + 1) *
        (memory * scales.hessian * scales.length (index.val + 1) ^ 2) *
          (600 * scales.omega (index.val + 1) * scales.length (index.val + 1) +
            (strain : ℝ) * (3 * scales.length (index.val + 1))) +
        8 * scales.circulation (index.val + 1) * (strain : ℝ) * (3 * scales.length (index.val + 1)) ^ 2 := by gcongr
    _ = (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) *
        (2400 * memory * scales.hessian * (scales.omega (index.val + 1) * scales.length (index.val + 1)) +
          12 * memory * scales.hessian * (strain : ℝ) * scales.length (index.val + 1) + 36 * (strain : ℝ)) := by ring
    _ ≤ (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) *
        (2400 * memory * scales.hessian + 12 * memory * (strain : ℝ) + 36 * (strain : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [mul_one] using add_le_add_right (add_le_add firstCost middleCost) (36 * (strain : ℝ))
    _ = _ := by dsimp only [strain]; simp only [NNReal.coe_mk]; ring

end EulerNonuniqueness.Paper.CascadeInternallyStoppedPath
