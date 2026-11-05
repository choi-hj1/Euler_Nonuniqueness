import EulerNonuniqueness.Section5.CascadeMechanicalDiagonalVelocity
import EulerNonuniqueness.Section5.CascadeRelativeDilationDynamics

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

namespace CascadeMaterialPreparedPair

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}

def pairedDiagonalVelocity
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) (side : Fin 2) : Fin count → ℝ → ℝ :=
  Fin.cases prepared.trajectory.quadrupoleDiagonalVelocity
    (fun _ => prepared.referenceWitness.trajectory.quadrupoleDiagonalVelocity) side

theorem pairedDiagonalVelocity_continuous
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) (side : Fin 2) (index : Fin count) :
    Continuous (prepared.pairedDiagonalVelocity side index) := by
  fin_cases side <;> exact MovingCentroidGaugeTrajectory.quadrupoleDiagonalVelocity_continuous _ index

theorem paired_diagonal_hasDerivAt
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) (side : Fin 2) (index : Fin count)
    {time : ℝ} (inside : time ∈ Ioo (-(1 : ℝ)) 3) :
    HasDerivAt (fun current => diagonalDifference (cascadePairedMotion prepared side) current index)
      (prepared.pairedDiagonalVelocity side index time) time := by
  fin_cases side
  · exact prepared.trajectory.diagonalDifference_hasDerivAt_quadrupoleDiagonalVelocity (fun _ => rfl) index inside
  · simpa only [cascadePairedMotion, pairedDiagonalVelocity, Fin.cases_succ, prepared.referenceIdentity] using
      prepared.referenceWitness.trajectory.diagonalDifference_hasDerivAt_quadrupoleDiagonalVelocity
        (fun _ => rfl) index inside

end CascadeMaterialPreparedPair

theorem Scales.eventually_cascade_relative_dilation_original_history (scales : Scales)
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
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count, index.val + 1 < count →
    ∀ time ∈ Icc 0 path.stop,
    (∀ current ∈ Icc 0 time, ∀ side,
      |unstableShape (cascadePairedMotion prepared side) current index| +
        |stableShape (cascadePairedMotion prepared side) current index| ≤ 1 / 4) →
    (diagonalDifference prepared.trajectory.movingFamily.patchMotion time index -
      diagonalDifference prepared.reference time index) /
        ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2 =
    ∫ current in (0 : ℝ)..time,
      (diagonalOddForcingRate {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion index current -
        diagonalOddForcingRate {scales with frequency := frequency} prepared.reference index current) /
          ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2 := by
  filter_upwards [scales.eventually_cascade_relative_dilation_dynamics amplitudePositive ratioBound alphaPositive
    rootPositive boundaryNonnegative factorPositive factorSmall thresholdSmall referenceNonnegative]
    with frequency actual
  intro orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path index nonterminal time inside small
  let lengthSquared := ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2
  let velocity := fun current =>
    (prepared.pairedDiagonalVelocity 0 index current - prepared.pairedDiagonalVelocity 1 index current) / lengthSquared
  have continuous : Continuous velocity :=
    ((prepared.pairedDiagonalVelocity_continuous 0 index).sub
      (prepared.pairedDiagonalVelocity_continuous 1 index)).div_const _
  have derivative (current : ℝ) (member : current ∈ Icc 0 time) :=
    ((prepared.paired_diagonal_hasDerivAt 0 index
      (show current ∈ Ioo (-(1 : ℝ)) 3 from ⟨by linarith [member.1], by linarith [member.2, inside.2, path.stopBound]⟩)).sub
    (prepared.paired_diagonal_hasDerivAt 1 index
      (show current ∈ Ioo (-(1 : ℝ)) 3 from ⟨by linarith [member.1], by linarith [member.2, inside.2, path.stopBound]⟩))).div_const lengthSquared
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le inside.1
    (fun current member => (derivative current member).continuousAt.continuousWithinAt)
    (fun current member => derivative current ⟨member.1.le, member.2.le⟩)
    (continuous.intervalIntegrable 0 time)
  change (∫ current in (0 : ℝ)..time, velocity current) =
    (diagonalDifference prepared.trajectory.movingFamily.patchMotion time index -
      diagonalDifference prepared.reference time index) / lengthSquared -
    (diagonalDifference prepared.trajectory.movingFamily.patchMotion 0 index -
      diagonalDifference prepared.reference 0 index) / lengthSquared at identity
  rw [(actual prepared path).1 index nonterminal, sub_zero] at identity
  apply identity.symm.trans
  apply intervalIntegral.integral_congr_ae
  have almostDifferent : ∀ᵐ current : ℝ ∂volume, current ≠ time := by simp [ae_iff]
  filter_upwards [almostDifferent] with current different
  intro member
  rw [uIoc_of_le inside.1] at member
  have closed : current ∈ Icc 0 time := ⟨member.1.le, member.2⟩
  have interior : current ∈ Ioo 0 path.stop :=
    ⟨member.1, (lt_of_le_of_ne member.2 different).trans_le inside.2⟩
  exact (derivative current closed).unique
    ((actual prepared path).2 index current interior (small current closed))

end EulerNonuniqueness.Paper
