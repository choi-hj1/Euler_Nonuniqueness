import EulerNonuniqueness.General.WeakClosedConvex
import EulerNonuniqueness.General.L2PairingContinuity

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace

namespace MeasureTheory

theorem isClosed_setOf_eLpNorm_le_on_Lp
    {Domain Value : Type*} [MeasurableSpace Domain] [NormedAddCommGroup Value]
    {measure : Measure Domain} {exponent topologyExponent bound : ℝ≥0∞}
    [Fact (1 ≤ topologyExponent)] :
    IsClosed {field : Lp Value topologyExponent measure |
      eLpNorm (field : Domain → Value) exponent measure ≤ bound} := by
  apply isSeqClosed_iff_isClosed.mp
  intro sequence limit inside converges
  obtain ⟨subsequence, increasing, almostEverywhere⟩ :=
    (tendstoInMeasure_of_tendsto_Lp converges).exists_seq_tendsto_ae
  exact (Lp.eLpNorm_lim_le_liminf_eLpNorm
    (fun index => Lp.aestronglyMeasurable (sequence (subsequence index))) limit almostEverywhere).trans
      (liminf_le_of_frequently_le' (Frequently.of_forall fun index => inside (subsequence index)))

theorem convex_setOf_eLpNorm_le_on_Lp
    {Domain Value : Type*} [MeasurableSpace Domain] [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] {measure : Measure Domain} {exponent topologyExponent bound : ℝ≥0∞}
    [Fact (1 ≤ topologyExponent)] (exponentBound : 1 ≤ exponent) :
    Convex ℝ {field : Lp Value topologyExponent measure |
      eLpNorm (field : Domain → Value) exponent measure ≤ bound} := by
  intro first firstInside second secondInside firstCoefficient secondCoefficient firstNonnegative
    secondNonnegative coefficientSum
  have representativeEquality :
      ((firstCoefficient • first + secondCoefficient • second : Lp Value topologyExponent measure) :
        Domain → Value) =ᵐ[measure]
        firstCoefficient • (first : Domain → Value) + secondCoefficient • (second : Domain → Value) := by
    filter_upwards [Lp.coeFn_add (firstCoefficient • first) (secondCoefficient • second),
      Lp.coeFn_smul firstCoefficient first, Lp.coeFn_smul secondCoefficient second]
      with point addition firstScaling secondScaling
    rw [addition, Pi.add_apply, firstScaling, secondScaling]
    rfl
  change eLpNorm _ exponent measure ≤ bound
  rw [eLpNorm_congr_ae representativeEquality]
  calc
    _ ≤ eLpNorm (firstCoefficient • (first : Domain → Value)) exponent measure +
        eLpNorm (secondCoefficient • (second : Domain → Value)) exponent measure :=
      eLpNorm_add_le ((Lp.aestronglyMeasurable first).const_smul firstCoefficient)
        ((Lp.aestronglyMeasurable second).const_smul secondCoefficient) exponentBound
    _ = ENNReal.ofReal firstCoefficient * eLpNorm (first : Domain → Value) exponent measure +
        ENNReal.ofReal secondCoefficient * eLpNorm (second : Domain → Value) exponent measure := by
      rw [eLpNorm_const_smul, eLpNorm_const_smul]
      simp only [← ofReal_norm_eq_enorm, Real.norm_of_nonneg firstNonnegative,
        Real.norm_of_nonneg secondNonnegative]
    _ ≤ ENNReal.ofReal firstCoefficient * bound + ENNReal.ofReal secondCoefficient * bound :=
      add_le_add (mul_le_mul_left' firstInside _) (mul_le_mul_left' secondInside _)
    _ = bound := by
      rw [← add_mul, ← ENNReal.ofReal_add firstNonnegative secondNonnegative, coefficientSum]
      simp

theorem eLpNorm_le_of_weakL2_tendsto
    {Domain Index : Type*} [MeasurableSpace Domain] {measure : Measure Domain}
    {filter : Filter Index} [filter.NeBot] {sequence : Index → Lp ℝ 2 measure}
    {limit : Lp ℝ 2 measure} {exponent bound : ℝ≥0∞}
    (exponentBound : 1 ≤ exponent)
    (bounded : ∀ index, eLpNorm (sequence index : Domain → ℝ) exponent measure ≤ bound)
    (weak : ∀ test : Lp ℝ 2 measure,
      Tendsto (fun index => ⟪sequence index, test⟫_ℝ) filter (𝓝 ⟪limit, test⟫_ℝ)) :
    eLpNorm (limit : Domain → ℝ) exponent measure ≤ bound := by
  exact (convex_setOf_eLpNorm_le_on_Lp (Domain := Domain) (Value := ℝ) (measure := measure)
    (topologyExponent := 2) (bound := bound) exponentBound).mem_of_weak_tendsto_of_isClosed
      (isClosed_setOf_eLpNorm_le_on_Lp (Domain := Domain) (Value := ℝ) (measure := measure)
        (topologyExponent := 2) (exponent := exponent) (bound := bound)) bounded weak

theorem eLpNorm_le_of_weakL2_tendsto_functions
    {Domain Index : Type*} [MeasurableSpace Domain] {measure : Measure Domain}
    {filter : Filter Index} [filter.NeBot] {sequence : Index → Domain → ℝ}
    {limit : Domain → ℝ} {exponent bound : ℝ≥0∞}
    (members : ∀ index, MemLp (sequence index) 2 measure) (limitMember : MemLp limit 2 measure)
    (exponentBound : 1 ≤ exponent)
    (bounded : ∀ index, eLpNorm (sequence index) exponent measure ≤ bound)
    (weak : ∀ test : Domain → ℝ, MemLp test 2 measure →
      Tendsto (fun index => ∫ point, sequence index point * test point ∂measure)
        filter (𝓝 (∫ point, limit point * test point ∂measure))) :
    eLpNorm limit exponent measure ≤ bound := by
  have operatorWeak (test : Lp ℝ 2 measure) : Tendsto
      (fun index => ⟪(members index).toLp (sequence index), test⟫_ℝ) filter
        (𝓝 ⟪limitMember.toLp limit, test⟫_ℝ) := by
    have testEquality : (Lp.memLp test).toLp (test : Domain → ℝ) = test := by simp
    have pairing (field : Domain → ℝ) (fieldMember : MemLp field 2 measure) :
        ⟪fieldMember.toLp field, test⟫_ℝ = ∫ point, field point * test point ∂measure := by
      calc
        _ = ⟪fieldMember.toLp field, (Lp.memLp test).toLp (test : Domain → ℝ)⟫_ℝ :=
          congrArg (fun other => ⟪fieldMember.toLp field, other⟫_ℝ) testEquality.symm
        _ = _ := inner_toLp_eq_integral_mul fieldMember (Lp.memLp test)
    simpa only [pairing] using weak test (Lp.memLp test)
  have normBound (index : Index) :
      eLpNorm ((members index).toLp (sequence index) : Domain → ℝ) exponent measure ≤ bound := by
    rw [eLpNorm_congr_ae (members index).coeFn_toLp]
    exact bounded index
  have result := eLpNorm_le_of_weakL2_tendsto exponentBound normBound operatorWeak
  rwa [eLpNorm_congr_ae limitMember.coeFn_toLp] at result

end MeasureTheory
