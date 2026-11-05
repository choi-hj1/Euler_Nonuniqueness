import EulerNonuniqueness.Section5.CascadeRhombusNeutralPrefix
import EulerNonuniqueness.Section5.CascadeRhombusAngularRate
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

def cascadeRhombusMemoryConstant : ℝ :=
  (497664 / Real.pi) * Real.exp (1152 / Real.pi)

def cascadeRhombusImpulseConstant : ℝ :=
  2400 * cascadeRhombusMemoryConstant +
    (12 * cascadeRhombusMemoryConstant + 36) * (1152 / Real.pi)

namespace CascadeInternallyStoppedPath

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
  {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
    scaleRoot shapeRadius factor monitor boundaryConstant count}

set_option maxHeartbeats 2000000

theorem rhombus_impulse_prefix_bound (path : CascadeInternallyStoppedPath prepared)
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
    (radiusLocation : ∀ source : Fin count, scales.radius (source.val + 1) ≤ scales.location (source.val + 1) / 1000)
    (omegaLength : scales.omega (index.val + 1) * scales.length (index.val + 1) ≤ 1)
    (strainBound : scales.strain ≤ 1) (hessianBound : scales.hessian ≤ 1) :
    ∀ time ∈ Icc 0 finish,
      |angularImpulse scales prepared.trajectory.movingFamily.patchMotion time index /
          (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) - 1| ≤
        cascadeRhombusImpulseConstant * (scales.strain + scales.hessian) * time := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have lengthPositive := scales.length_pos (index.val + 1)
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ scales.hessian := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (scales.location_pos _).le _)
  have memoryNonnegative : 0 ≤ cascadeRhombusMemoryConstant := by unfold cascadeRhombusMemoryConstant; positivity
  have secondaryNonnegative : 0 ≤ (12 * cascadeRhombusMemoryConstant + 36) * (1152 / Real.pi) := by positivity
  have neutral := path.rhombus_neutral_prefix_bound amplitudePositive frequencyBound ratioBound alphaPositive
    thresholdSmall factorSmall index nonterminal finishNonnegative finishBound differenceLower differenceUpper
    radialSmall asymmetrySmall lengthSmall radiusSmall radiusLocation
  have timeRange {time : ℝ} (member : time ∈ Icc 0 finish) : time ∈ Icc 0 path.stop :=
    ⟨member.1, member.2.trans finishBound⟩
  have globalInside {time : ℝ} (member : time ∈ Icc 0 finish) : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [member.1], by linarith [member.2, finishBound, path.stopBound]⟩
  have improvedNeutral (time : ℝ) (member : time ∈ Icc 0 finish) :
      ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index‖ ≤
        cascadeRhombusMemoryConstant * scales.hessian * scales.length (index.val + 1) ^ 2 := by
    have timeBound : time ≤ 1 := member.2.trans (finishBound.trans path.stopBound)
    apply (neutral time member).trans
    calc
      _ ≤ (497664 / Real.pi) * scales.hessian * scales.length (index.val + 1) ^ 2 * 1 *
          Real.exp (((1152 / Real.pi) * 1) * 1) := by gcongr; exact member.1
      _ = _ := by unfold cascadeRhombusMemoryConstant; ring
  have rateBound :
      2400 * cascadeRhombusMemoryConstant * scales.hessian +
        (12 * cascadeRhombusMemoryConstant + 36) * (1152 / Real.pi) * scales.strain ≤
      cascadeRhombusImpulseConstant * (scales.strain + scales.hessian) := by
    have first := mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right secondaryNonnegative :
        2400 * cascadeRhombusMemoryConstant ≤ cascadeRhombusImpulseConstant) hessianNonnegative
    have second := mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (by positivity : 0 ≤ 2400 * cascadeRhombusMemoryConstant) :
        (12 * cascadeRhombusMemoryConstant + 36) * (1152 / Real.pi) ≤ cascadeRhombusImpulseConstant) strainNonnegative
    exact (add_le_add first second).trans_eq (by unfold cascadeRhombusImpulseConstant; ring)
  let denominator := 2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2
  have denominatorPositive : 0 < denominator := by dsimp only [denominator]; positivity
  let function := fun current => angularImpulse scales prepared.trajectory.movingFamily.patchMotion current index / denominator
  have derivative (time : ℝ) (member : time ∈ Icc 0 finish) :
      HasDerivAt function
        (deriv (fun current => angularImpulse scales prepared.trajectory.movingFamily.patchMotion current index) time / denominator) time := by
    have material (label : Fin (count * 4)) (angle : ℝ) := path.material_boundary (timeRange member) label angle
    rw [prepared.trajectory.movingFamily.patchVorticity_eq scales prepared.densityIdentity] at material
    have actual := prepared.trajectory.movingFamily.quadrupole_angularImpulse_hasDerivAt_external scales
      prepared.densityIdentity (fun _ => globalInside member) material index
    exact actual.differentiableAt.hasDerivAt.div_const denominator
  have bound (time : ℝ) (member : time ∈ Ico 0 finish) :
      ‖deriv (fun current => angularImpulse scales prepared.trajectory.movingFamily.patchMotion current index) time / denominator‖ ≤ cascadeRhombusImpulseConstant * (scales.strain + scales.hessian) := by
    have member : time ∈ Icc 0 finish := ⟨member.1, member.2.le⟩
    rw [Real.norm_eq_abs, abs_div, abs_of_pos denominatorPositive]
    have actual := path.rhombus_angularImpulse_deriv_scale_bound amplitudePositive frequencyBound ratioBound alphaPositive
      factorSmall (timeRange member) index (differenceLower time member) (differenceUpper time member)
      (radialSmall time member) (asymmetrySmall time member) lengthSmall radiusSmall radiusLocation
      memoryNonnegative (improvedNeutral time member) omegaLength hessianBound
    apply (div_le_iff₀ denominatorPositive).mpr
    exact actual.trans ((mul_le_mul_of_nonneg_left rateBound denominatorPositive.le).trans_eq (mul_comm _ _))
  intro time member
  have estimate := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun current currentInside => (derivative current currentInside).hasDerivWithinAt) bound time member
  have initial := (prepared.nonterminal_initial_invariants amplitudePositive frequencyPositive ratioPositive
    thresholdSmall index nonterminal).2.2
  have initialNormalized : function 0 = 1 := by
    dsimp only [function]
    rw [initial]
    exact div_self denominatorPositive.ne'
  rw [initialNormalized, sub_zero] at estimate
  simpa only [function, Real.norm_eq_abs] using estimate

end CascadeInternallyStoppedPath

end EulerNonuniqueness.Paper

