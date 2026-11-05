import EulerNonuniqueness.Section5.CascadeRhombusImpulsePrefix
import EulerNonuniqueness.Section4.ReferenceDiagonalDeformationScale

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.CascadeInternallyStoppedPath

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
  {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
    scaleRoot shapeRadius factor monitor boundaryConstant count}

theorem rhombus_diagonal_prefix_numeric_bound (path : CascadeInternallyStoppedPath prepared)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (thresholdSmall : threshold ≤ 1 / 2) (factorSmall : factor ≤ 1 / 8)
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
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
    (strainBound : scales.strain ≤ 1) (hessianBound : scales.hessian ≤ 1)
    (boundarySmall : boundaryConstant / (scaleRoot ^ 2 * scales.omega (index.val + 1) ^ 2) ≤ 1 / 16)
 :
    ∀ time ∈ Icc 0 finish,
      |diagonalDifference prepared.trajectory.movingFamily.patchMotion time index /
        scales.length (index.val + 1) ^ 2 - 1| ≤ cascadeRhombusImpulseConstant * (scales.strain + scales.hessian) +
        48 * (boundaryConstant / scaleRoot ^ 2) ^ 2 / (scales.amplitude * scales.frequency ^ 7) := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have deformationNonnegative : 0 ≤ boundaryConstant / (scaleRoot ^ 2 * scales.omega (index.val + 1) ^ 2) := by positivity
  have impulse := path.rhombus_impulse_prefix_bound amplitudePositive frequencyBound ratioBound alphaPositive
    thresholdSmall factorSmall index nonterminal finishNonnegative finishBound differenceLower differenceUpper
    radialSmall asymmetrySmall lengthSmall radiusSmall radiusLocation omegaLength strainBound hessianBound
  have deformation := scales.reference_diagonal_deformation_cost_le amplitudePositive frequencyPositive
    (by linarith : 1 ≤ scales.ratio) (index.val + 1) deformationNonnegative
    (show boundaryConstant / (scaleRoot ^ 2 * scales.omega (index.val + 1) ^ 2) ≤
      (boundaryConstant / scaleRoot ^ 2) / scales.omega (index.val + 1) ^ 2 by
      rw [div_div])
  intro time member
  have inside : time ∈ Icc 0 path.stop := ⟨member.1, member.2.trans finishBound⟩
  have inertia := path.evolution.reference_diagonal_impulse_error inside amplitudePositive frequencyPositive
    ratioPositive index (path.boundary time inside index) deformationNonnegative boundarySmall
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ scales.hessian := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (scales.location_pos _).le _)
  have impulseNonnegative : 0 ≤ cascadeRhombusImpulseConstant * (scales.strain + scales.hessian) := by
    unfold cascadeRhombusImpulseConstant cascadeRhombusMemoryConstant
    positivity
  have timeBound : time ≤ 1 := member.2.trans (finishBound.trans path.stopBound)
  exact (inertia.trans (add_le_add (impulse time member) deformation)).trans
    (add_le_add_right (mul_le_of_le_one_right impulseNonnegative timeBound) _)

end EulerNonuniqueness.Paper.CascadeInternallyStoppedPath

