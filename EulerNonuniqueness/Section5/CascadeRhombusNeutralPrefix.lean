import EulerNonuniqueness.Section5.CascadeRhombusOwnGeometry
import EulerNonuniqueness.Section5.CascadeRhombusForeignGeometry
import EulerNonuniqueness.Section5.CascadeNeutralVelocity
import EulerNonuniqueness.Section5.CascadeNonterminalInitialMoments
import EulerNonuniqueness.Section6.MovingQuadrupoleMemoryBound
import EulerNonuniqueness.General.InteriorNormGronwall
import EulerNonuniqueness.Section1.ForeignInteractionWeight

noncomputable section

open Set Metric
open scoped NNReal Topology

namespace EulerNonuniqueness.Paper.CascadeInternallyStoppedPath

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
  {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
    scaleRoot shapeRadius factor monitor boundaryConstant count}

set_option maxHeartbeats 2000000

theorem rhombus_neutral_prefix_bound (path : CascadeInternallyStoppedPath prepared)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (thresholdSmall : threshold ≤ 1 / 2) (factorSmall : factor ≤ 1 / 8)
    (index : Fin count) (nonterminal : index.val + 1 < count) {finish : ℝ}
    (finishNonnegative : 0 ≤ finish) (finishBound : finish ≤ path.stop)
    (differenceLower : ∀ time ∈ Icc 0 finish, scales.length (index.val + 1) ^ 2 / 2 ≤
      diagonalDifference prepared.trajectory.movingFamily.patchMotion time index)
    (differenceUpper : ∀ time ∈ Icc 0 finish, diagonalDifference prepared.trajectory.movingFamily.patchMotion time index ≤
      2 * scales.length (index.val + 1) ^ 2)
    (radialSmall : ∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2)
    (asymmetrySmall : ∀ time ∈ Icc 0 finish, ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index‖ ≤
      scales.length (index.val + 1) / 64)
    (lengthSmall : scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (radiusSmall : scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000)
    (radiusLocation : ∀ source : Fin count, scales.radius (source.val + 1) ≤ scales.location (source.val + 1) / 1000) :
    ∀ time ∈ Icc 0 finish, ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index‖ ≤
      ((497664 / Real.pi) * scales.hessian * scales.length (index.val + 1) ^ 2 * time) *
        Real.exp (((1152 / Real.pi) * scales.strain) * time) := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have lengthPositive := scales.length_pos (index.val + 1)
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ scales.hessian := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (scales.location_pos _).le _)
  have initial := (prepared.nonterminal_initial_invariants amplitudePositive frequencyPositive ratioPositive thresholdSmall index nonterminal).1
  by_cases zero : finish = 0
  · subst finish
    intro time member
    have timeZero : time = 0 := le_antisymm member.2 member.1
    simp only [timeZero, initial, norm_zero, mul_zero, Real.exp_zero, mul_one, le_refl]
  have finishPositive : 0 < finish := lt_of_le_of_ne finishNonnegative (Ne.symm zero)
  have timeRange {time : ℝ} (member : time ∈ Icc 0 finish) : time ∈ Icc 0 path.stop :=
    ⟨member.1, member.2.trans finishBound⟩
  have globalInside {time : ℝ} (member : time ∈ Icc 0 finish) : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [member.1], by linarith [member.2, finishBound, path.stopBound]⟩
  let strain : ℝ≥0 := ⟨(1152 / Real.pi) * scales.strain, by positivity⟩
  let distance : Fin count → ℝ := fun source =>
    |scales.location (index.val + 1) - scales.location (source.val + 1)| / 8
  have differential (time : ℝ) (member : time ∈ Icc 0 finish) :
      ‖prepared.neutralVelocity index time‖ ≤
        ((1152 / Real.pi) * scales.strain) * ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index‖ +
          (497664 / Real.pi) * scales.hessian * scales.length (index.val + 1) ^ 2 := by
    have own := path.rhombus_own_domain_geometry (timeRange member) index
      (differenceLower time member) (differenceUpper time member) (radialSmall time member)
      (asymmetrySmall time member) radiusSmall factorSmall
    have foreign (source : Fin count) (sourceMember : source ∈ Finset.univ.erase index) :=
      path.rhombus_ball_foreign_geometry (timeRange member) index lengthSmall radiusLocation source
        (Finset.mem_erase.mp sourceMember).1
    have positive (source : Fin count) (sourceMember : source ∈ Finset.univ.erase index) : 0 < distance source :=
      div_pos (scales.location_distance_pos (fun equality =>
        (Finset.mem_erase.mp sourceMember).1 (Fin.ext (Nat.add_right_cancel equality).symm))) (by norm_num)
    have material (label : Fin (count * 4)) (angle : ℝ) := path.material_boundary (timeRange member) label angle
    rw [prepared.trajectory.movingFamily.patchVorticity_eq scales prepared.densityIdentity] at material
    obtain ⟨error, derivative, errorBound⟩ :=
      prepared.trajectory.movingFamily.centroidAsymmetry_external_linearization_closed scales prepared.densityIdentity
        path.evolution path.stopPositive (timeRange member) amplitudePositive frequencyPositive ratioPositive
        (fun _ => globalInside member) material index
        (quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index)
        (by positivity : 0 ≤ 3 * scales.length (index.val + 1)) own.2 distance positive
        (fun source sourceMember => (foreign source sourceMember).2 _ (mem_closedBall_self (by positivity)))
        (fun source sourceMember => by
          change 2 * (3 * scales.length (index.val + 1)) ≤
            |scales.location (index.val + 1) - scales.location (source.val + 1)| / 8
          nlinarith only [(foreign source sourceMember).1])
    have lipschitz := path.evolution.externalPatch_biotSavart_lipschitzOn (timeRange member)
      amplitudePositive frequencyPositive ratioPositive index distance
      (closedBall (quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index) (3 * scales.length (index.val + 1)))
      (bound := strain) positive (fun position positionInside source sourceMember =>
        (foreign source sourceMember).2 position positionInside)
      (scales.foreign_strain_weight_le frequencyBound ratioBound alphaPositive index)
    have operatorBound := norm_fderiv_le_of_lipschitzOn ℝ
      (closedBall_mem_nhds _ (by positivity : 0 < 3 * scales.length (index.val + 1))) lipschitz
    have identity := (prepared.centroidAsymmetry_hasDerivAt_velocity index (globalInside member)).unique derivative
    rw [identity]
    have linearBound : ‖(fderiv ℝ
        (biotSavart (externalPatchVorticity scales prepared.trajectory.movingFamily.patchMotion time index))
        (quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index))
        (centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index)‖ ≤
        (strain : ℝ) * ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right operatorBound (norm_nonneg _))
    have remainderBound := errorBound.trans
      (mul_le_mul_of_nonneg_right (scales.foreign_hessian_weight_le frequencyBound ratioBound alphaPositive index)
        (sq_nonneg (3 * scales.length (index.val + 1))))
    exact (norm_add_le _ _).trans ((add_le_add linearBound remainderBound).trans_eq (by
      dsimp only [strain]
      simp only [NNReal.coe_mk]
      ring))
  have bound := EulerNonuniqueness.General.norm_constant_forcing_gronwall_of_interior_derivative
    finishPositive (by positivity : 0 ≤ (1152 / Real.pi) * scales.strain)
    (by positivity : 0 ≤ (497664 / Real.pi) * scales.hessian * scales.length (index.val + 1) ^ 2)
    (fun time member => (prepared.centroidAsymmetry_hasDerivAt_velocity index (globalInside member)).continuousAt.continuousWithinAt)
    (prepared.neutralVelocity_continuous index).continuousOn
    (fun time member => prepared.centroidAsymmetry_hasDerivAt_velocity index (globalInside ⟨member.1.le, member.2.le⟩))
    (fun time member => differential time ⟨member.1.le, member.2.le⟩)
  simpa only [initial, norm_zero, zero_add] using bound

end EulerNonuniqueness.Paper.CascadeInternallyStoppedPath
