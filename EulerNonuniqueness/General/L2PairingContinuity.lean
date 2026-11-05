import EulerNonuniqueness.General.MovingLinearPairing
import EulerNonuniqueness.General.WeakLpConvergence

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace

namespace MeasureTheory

theorem inner_toLp_eq_integral_mul {Domain : Type*} [MeasurableSpace Domain]
    {measure : Measure Domain} {first second : Domain → ℝ}
    (firstMember : MemLp first 2 measure) (secondMember : MemLp second 2 measure) :
    ⟪firstMember.toLp first, secondMember.toLp second⟫_ℝ =
      ∫ point, first point * second point ∂measure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [firstMember.coeFn_toLp, secondMember.coeFn_toLp] with point firstEquality secondEquality
  simp [firstEquality, secondEquality, RCLike.inner_apply, mul_comm]

theorem tendsto_integral_mul_of_strongL2
    {Domain Index : Type*} [MeasurableSpace Domain] {measure : Measure Domain}
    {filter : Filter Index} {sequence : Index → Domain → ℝ} {limit test : Domain → ℝ}
    (members : ∀ index, MemLp (sequence index) 2 measure)
    (limitMember : MemLp limit 2 measure) (testMember : MemLp test 2 measure)
    (converges : Tendsto (fun index => eLpNorm (sequence index - limit) 2 measure) filter (𝓝 0)) :
    Tendsto (fun index => ∫ point, sequence index point * test point ∂measure)
      filter (𝓝 (∫ point, limit point * test point ∂measure)) := by
  have quotientConverges :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' sequence members limit limitMember).mpr converges
  have pairingConverges : Tendsto
      (fun index => ⟪(members index).toLp (sequence index), testMember.toLp test⟫_ℝ) filter
      (𝓝 ⟪limitMember.toLp limit, testMember.toLp test⟫_ℝ) :=
    quotientConverges.inner (tendsto_const_nhds (x := testMember.toLp test))
  simpa only [inner_toLp_eq_integral_mul] using pairingConverges

theorem tendsto_integral_mul_of_weakL2_strongL2
    {Domain Index : Type*} [MeasurableSpace Domain] {measure : Measure Domain}
    {filter : Filter Index} {sequence tests : Index → Domain → ℝ}
    {limit test : Domain → ℝ} {bound : ℝ}
    (members : ∀ index, MemLp (sequence index) 2 measure)
    (testMembers : ∀ index, MemLp (tests index) 2 measure)
    (testMember : MemLp test 2 measure)
    (bounded : ∀ index, (eLpNorm (sequence index) 2 measure).toReal ≤ bound)
    (weak : ∀ fixedTest : Domain → ℝ, MemLp fixedTest 2 measure →
      Tendsto (fun index => ∫ point, sequence index point * fixedTest point ∂measure)
        filter (𝓝 (∫ point, limit point * fixedTest point ∂measure)))
    (strong : Tendsto (fun index => eLpNorm (tests index - test) 2 measure) filter (𝓝 0)) :
    Tendsto (fun index => ∫ point, sequence index point * tests index point ∂measure)
      filter (𝓝 (∫ point, limit point * test point ∂measure)) := by
  have realExponent : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  let operators : Index → Lp ℝ (ENNReal.ofReal (2 : ℝ)) measure →L[ℝ] ℝ := fun index =>
    integralSmulCLM Real.HolderConjugate.two_two
      (show MemLp (sequence index) (ENNReal.ofReal (2 : ℝ)) measure by
        simpa only [realExponent] using members index)
  have operatorBound (index : Index) : ‖operators index‖ ≤ bound := by
    exact (norm_integralSmulCLM_le Real.HolderConjugate.two_two _).trans
      (by simpa only [realExponent] using bounded index)
  have evaluate (index : Index) (field : Domain → ℝ)
      (fieldMember : MemLp field (ENNReal.ofReal (2 : ℝ)) measure) :
      operators index (fieldMember.toLp field) =
        ∫ point, sequence index point * field point ∂measure := by
    change (∫ point, sequence index point • fieldMember.toLp field point ∂measure) = _
    apply integral_congr_ae
    filter_upwards [fieldMember.coeFn_toLp] with point equality
    simp only [equality, smul_eq_mul]
  let convertedMembers : ∀ index, MemLp (tests index) (ENNReal.ofReal (2 : ℝ)) measure :=
    fun index => by simpa only [realExponent] using testMembers index
  let convertedMember : MemLp test (ENNReal.ofReal (2 : ℝ)) measure := by
    simpa only [realExponent] using testMember
  have argumentsConverge :
      Tendsto (fun index => (convertedMembers index).toLp (tests index)) filter
        (𝓝 (convertedMember.toLp test)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' tests convertedMembers test convertedMember).mpr
      (by simpa only [realExponent] using strong)
  have fixedConverges : Tendsto (fun index => operators index (convertedMember.toLp test))
      filter (𝓝 (∫ point, limit point * test point ∂measure)) := by
    simpa only [evaluate] using weak test testMember
  have result := ContinuousLinearMap.tendsto_apply_moving_of_bounded operatorBound
    fixedConverges argumentsConverge
  simpa only [evaluate] using result

end MeasureTheory
