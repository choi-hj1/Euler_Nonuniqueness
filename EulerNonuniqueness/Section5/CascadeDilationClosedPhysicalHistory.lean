import EulerNonuniqueness.Section6.MovingDilationPhysicalDerivative
import EulerNonuniqueness.Section5.CascadeDilationPhysicalHistory
import EulerNonuniqueness.Section5.CascadeNonterminalInitialMoments

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem Scales.eventually_cascade_dilation_closed_physical_history (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {threshold referenceConstant factor : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (factorPositive : 0 < factor) :
    ∀ᶠ frequency : ℝ in atTop,
      ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
        {scaleRoot shapeRadius monitor boundaryConstant : ℝ} {count : ℕ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count, index.val + 1 < count →
      ∀ time ∈ Icc 0 path.stop,
      let changed : Scales := {scales with frequency := frequency}
      HasDerivAt (fun current => (diagonalDifference prepared.trajectory.movingFamily.patchMotion current index -
          diagonalDifference prepared.reference current index) / changed.length (index.val + 1) ^ 2)
        (relativeDilationPhysicalVelocity changed prepared.trajectory.movingFamily.patchMotion prepared.reference index time) time ∧
      (diagonalDifference prepared.trajectory.movingFamily.patchMotion time index - diagonalDifference prepared.reference time index) /
          changed.length (index.val + 1) ^ 2 =
        ∫ current in (0 : ℝ)..time,
          relativeDilationPhysicalVelocity changed prepared.trajectory.movingFamily.patchMotion prepared.reference index current := by
  filter_upwards [scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive
      thresholdSmall referenceNonnegative] with frequency mechanical
  intro orbit sectionTime phase dipoleAngle scaleRoot shapeRadius monitor boundaryConstant count prepared path index nonterminal time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let velocity := fun current =>
    (prepared.pairedDiagonalVelocity 0 index current - prepared.pairedDiagonalVelocity 1 index current) /
      changed.length (index.val + 1) ^ 2
  have physical (current : ℝ) (member : current ∈ Icc 0 path.stop) :
      velocity current = relativeDilationPhysicalVelocity changed prepared.trajectory.movingFamily.patchMotion prepared.reference index current := by
    have globalInside : current ∈ Ioo (-(1 : ℝ)) 3 :=
      ⟨by linarith [member.1], by linarith [member.2, path.stopBound]⟩
    have actualNoncollision : FourPointNoncollision (fun patch => patchCentroid prepared.trajectory.movingFamily.patchMotion current index patch) := by
      intro first second different equality
      have gap := path.internal_centroid_gap member index first second (Ne.symm different)
      rw [equality, norm_zero] at gap
      exact (mul_pos factorPositive (changed.length_pos _)).not_le gap
    have referenceInside : current ∈ Icc (0 : ℝ) 2 := ⟨member.1, by linarith [member.2, path.stopBound]⟩
    have referenceData := mechanical prepared.referenceWitness.trajectory.movingFamily.patchMotion
      prepared.referenceWitness.evolution prepared.referenceWitness.coarse current referenceInside index
    have referenceNoncollision : FourPointNoncollision (fun patch =>
        patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current index patch) := by
      intro first second different equality
      have gap := referenceData.1.internalSeparated first second different
      rw [equality, norm_zero] at gap
      exact (div_pos (changed.length_pos _) (by norm_num : (0 : ℝ) < 100)).not_le gap
    have firstDerivative := prepared.trajectory.movingFamily.diagonalDifference_hasDerivAt_physical_rate
      path.evolution member index (fun _ => globalInside)
      (fun patch label => path.material_boundary member (finProdFinEquiv (index, patch)) label) actualNoncollision
    have secondDerivative := prepared.referenceWitness.trajectory.movingFamily.diagonalDifference_hasDerivAt_physical_rate
      (prepared.referenceWitness.evolution.mono (show path.stop ≤ 2 by linarith [path.stopBound])) member index
      (fun _ => globalInside) (fun patch label => by
        rw [prepared.referenceWitness.trajectory.movingFamily.patchVorticity_eq changed prepared.referenceWitness.densityIdentity]
        exact prepared.referenceWitness.trajectory.movingFamily_material_equation_of_margin prepared.referenceWitness.marginPositive
          globalInside (prepared.referenceWitness.safe current referenceInside) (finProdFinEquiv (index, patch)) label)
      referenceNoncollision
    have firstIdentity := (prepared.paired_diagonal_hasDerivAt 0 index globalInside).unique firstDerivative
    have secondIdentity := (prepared.paired_diagonal_hasDerivAt 1 index globalInside).unique
      (by simpa only [cascadePairedMotion, Fin.cases_succ, prepared.referenceIdentity] using secondDerivative)
    dsimp only [velocity, relativeDilationPhysicalVelocity]
    rw [firstIdentity, secondIdentity]
    rw [prepared.referenceIdentity]
    ring
  have derivative (current : ℝ) (member : current ∈ Icc 0 path.stop) :=
    ((prepared.paired_diagonal_hasDerivAt 0 index
      (show current ∈ Ioo (-(1 : ℝ)) 3 by constructor <;> linarith [member.1, member.2, path.stopBound])).sub
      (prepared.paired_diagonal_hasDerivAt 1 index
        (show current ∈ Ioo (-(1 : ℝ)) 3 by constructor <;> linarith [member.1, member.2, path.stopBound]))).div_const
        (changed.length (index.val + 1) ^ 2)
  constructor
  · have actual := derivative time inside
    change HasDerivAt _ (velocity time) time at actual
    rw [physical time inside] at actual
    exact actual
  · have continuous : Continuous velocity := ((prepared.pairedDiagonalVelocity_continuous 0 index).sub
        (prepared.pairedDiagonalVelocity_continuous 1 index)).div_const _
    have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le inside.1
      (fun current member => (derivative current ⟨member.1, member.2.trans inside.2⟩).continuousAt.continuousWithinAt)
      (fun current member => derivative current ⟨member.1.le, member.2.le.trans inside.2⟩)
      (continuous.intervalIntegrable 0 time)
    have initial : diagonalDifference prepared.trajectory.movingFamily.patchMotion 0 index =
        diagonalDifference prepared.reference 0 index := by
      simp only [diagonalDifference, positiveHalfDiagonal, negativeHalfDiagonal,
        prepared.nonterminal_initial_centroid index nonterminal]
    change (∫ current in (0 : ℝ)..time, velocity current) =
      (diagonalDifference prepared.trajectory.movingFamily.patchMotion time index -
        diagonalDifference prepared.reference time index) / changed.length (index.val + 1) ^ 2 -
      (diagonalDifference prepared.trajectory.movingFamily.patchMotion 0 index -
        diagonalDifference prepared.reference 0 index) / changed.length (index.val + 1) ^ 2 at identity
    rw [initial, sub_self, zero_div, sub_zero] at identity
    apply identity.symm.trans
    apply intervalIntegral.integral_congr
    intro current member
    exact physical current ⟨(uIcc_of_le inside.1 ▸ member).1, (uIcc_of_le inside.1 ▸ member).2.trans inside.2⟩

end EulerNonuniqueness.Paper
