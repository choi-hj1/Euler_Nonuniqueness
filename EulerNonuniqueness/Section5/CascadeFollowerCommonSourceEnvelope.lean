import EulerNonuniqueness.Section5.CascadeSelectedForcingSingletonSum
import EulerNonuniqueness.Section5.CascadeFollowerDrivenEnvelopeVolterra

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem CascadeSourcePreparedPair.followerStrictlyFinerForcing_le_common_source_envelope
    {cap : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
    {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    (prepared : CascadeSourcePreparedPair cap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (drive : Fin count) (time : ℝ) (envelope : Fin count → ℝ)
    (nonnegative : ∀ source, drive.val < source.val → 0 ≤ envelope source)
    (commonBound : ∀ receiver : Fin count, receiver.val < drive.val →
      ∀ source : Fin count, drive.val < source.val →
        scales.location (receiver.val + 1) ^ 4 * prepared.selectedForeignForcing {source} receiver time ≤ envelope source) :
    prepared.followerStrictlyFinerForcing drive time ≤
      ∑ source ∈ Finset.univ.filter (fun source : Fin count => drive.val < source.val), envelope source := by
  let sources := Finset.univ.filter (fun source : Fin count => drive.val < source.val)
  have sumNonnegative : 0 ≤ ∑ source ∈ sources, envelope source :=
    Finset.sum_nonneg fun source member => nonnegative source (Finset.mem_filter.mp member).2
  have forcingNonnegative (selected : Finset (Fin count)) (receiver : Fin count) :
      0 ≤ prepared.selectedForeignForcing selected receiver time := by
    have locationPositive := scales.location_pos (receiver.val + 1)
    dsimp only [CascadeSourcePreparedPair.selectedForeignForcing,
      CascadeSourcePreparedPair.coarserBlockCoefficientTerm, CascadeSourcePreparedPair.coarserPatchCoefficientTerm]
    positivity
  dsimp only [CascadeSourcePreparedPair.followerStrictlyFinerForcing]
  apply (pi_norm_le_iff_of_nonneg sumNonnegative).mpr
  intro receiver
  by_cases follower : receiver.val < drive.val
  · have selectedIdentity : Finset.univ.filter (fun source : Fin count => drive.val < source.val ∧ source ≠ receiver) = sources := by
      ext source
      simp only [sources, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun member => member.1
      · intro finer
        refine ⟨finer, ?_⟩
        intro equality
        have sameValue := congrArg Fin.val equality
        omega
    have scaleNonnegative : 0 ≤ scales.location (receiver.val + 1) ^ 4 := pow_nonneg (scales.location_pos _).le 4
    simp only [follower, ite_true, selectedIdentity, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg scaleNonnegative (forcingNonnegative sources receiver))]
    calc
      _ ≤ scales.location (receiver.val + 1) ^ 4 *
          (∑ source ∈ sources, prepared.selectedForeignForcing {source} receiver time) :=
        mul_le_mul_of_nonneg_left (prepared.selectedForeignForcing_le_sum_singletons sources receiver time) scaleNonnegative
      _ = ∑ source ∈ sources, scales.location (receiver.val + 1) ^ 4 *
          prepared.selectedForeignForcing {source} receiver time := Finset.mul_sum _ _ _
      _ ≤ ∑ source ∈ sources, envelope source :=
        Finset.sum_le_sum fun source member => commonBound receiver follower source (Finset.mem_filter.mp member).2
  · simp only [follower, ite_false, norm_zero]
    exact sumNonnegative

end EulerNonuniqueness.Paper
