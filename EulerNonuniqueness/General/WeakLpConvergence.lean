import EulerNonuniqueness.General.ConvolutionContinuity

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace ContinuousLinearMap

theorem tendsto_apply_of_tendsto_on_dense
    {Domain Value Index : Type*} [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {filter : Filter Index} {operators : Index → Domain →L[ℝ] Value}
    {limit : Domain →L[ℝ] Value} {denseSet : Set Domain} {bound : ℝ}
    (dense : Dense denseSet) (bounded : ∀ index, ‖operators index‖ ≤ bound)
    (converges : ∀ point ∈ denseSet,
      Tendsto (fun index => operators index point) filter (𝓝 (limit point))) (point : Domain) :
    Tendsto (fun index => operators index point) filter (𝓝 (limit point)) := by
  apply Metric.tendsto_nhds.mpr
  intro tolerance tolerancePositive
  let coefficient := max bound 0 + ‖limit‖ + 1
  have coefficientPositive : 0 < coefficient := by dsimp [coefficient]; positivity
  obtain ⟨approximation, inside, close⟩ := dense.exists_dist_lt point
    (show 0 < tolerance / (3 * coefficient) by positivity)
  filter_upwards [Metric.tendsto_nhds.mp (converges approximation inside)
    (tolerance / 3) (by positivity)] with index middle
  have firstBound : dist (operators index point) (operators index approximation) ≤
      max bound 0 * dist point approximation := by
    simpa only [dist_eq_norm, map_sub] using
      ((operators index).le_opNorm (point - approximation)).trans
        (mul_le_mul_of_nonneg_right ((bounded index).trans (le_max_left bound 0))
          (norm_nonneg (point - approximation)))
  have lastBound : dist (limit approximation) (limit point) ≤
      ‖limit‖ * dist point approximation := by
    rw [dist_comm]
    simpa only [dist_eq_norm, map_sub] using limit.le_opNorm (point - approximation)
  have productSmall : coefficient * dist point approximation < tolerance / 3 := by
    have estimate := mul_lt_mul_of_pos_left close coefficientPositive
    have identity : coefficient * (tolerance / (3 * coefficient)) = tolerance / 3 := by
      field_simp
      ring
    rwa [identity] at estimate
  have triangle := (dist_triangle (operators index point) (operators index approximation)
    (limit point)).trans (add_le_add_left
      (dist_triangle (operators index approximation) (limit approximation) (limit point)) _)
  dsimp [coefficient] at productSmall
  nlinarith [dist_nonneg (x := point) (y := approximation)]

end ContinuousLinearMap

namespace MeasureTheory

theorem integralSmulCLM_toLp {Domain Value : Type*}
    [MeasurableSpace Domain] [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {measure : Measure Domain} {exponent conjugate : ℝ}
    [Fact (1 ≤ ENNReal.ofReal conjugate)] {weight : Domain → ℝ} {field : Domain → Value}
    (conjugacy : exponent.HolderConjugate conjugate)
    (weightMember : MemLp weight (ENNReal.ofReal exponent) measure)
    (fieldMember : MemLp field (ENNReal.ofReal conjugate) measure) :
    integralSmulCLM conjugacy weightMember (fieldMember.toLp field) =
      ∫ point, weight point • field point ∂measure := by
  change (∫ point, weight point • fieldMember.toLp field point ∂measure) = _
  apply integral_congr_ae
  filter_upwards [fieldMember.coeFn_toLp] with point equality
  rw [equality]

theorem tendsto_integral_mul_of_weakL2_of_uniform_memLp
    {Domain Index : Type*} [MeasurableSpace Domain] {measure : Measure Domain}
    {filter : Filter Index} {sequence : Index → Domain → ℝ} {limit : Domain → ℝ}
    {exponent conjugate bound : ℝ}
    (conjugacy : exponent.HolderConjugate conjugate)
    (members : ∀ index, MemLp (sequence index) (ENNReal.ofReal exponent) measure)
    (limitMember : MemLp limit (ENNReal.ofReal exponent) measure)
    (bounded : ∀ index,
      (eLpNorm (sequence index) (ENNReal.ofReal exponent) measure).toReal ≤ bound)
    (weak : ∀ test : Domain → ℝ, MemLp test 2 measure →
      Tendsto (fun index => ∫ point, sequence index point * test point ∂measure) filter
        (𝓝 (∫ point, limit point * test point ∂measure)))
    {test : Domain → ℝ} (testMember : MemLp test (ENNReal.ofReal conjugate) measure) :
    Tendsto (fun index => ∫ point, sequence index point * test point ∂measure) filter
      (𝓝 (∫ point, limit point * test point ∂measure)) := by
  letI : Fact (1 ≤ ENNReal.ofReal conjugate) := ⟨by
    exact_mod_cast ENNReal.ofReal_le_ofReal conjugacy.symm.lt.le⟩
  let operators := fun index => integralSmulCLM (Value := ℝ) conjugacy (members index)
  let limitOperator := integralSmulCLM (Value := ℝ) conjugacy limitMember
  have converges : ∀ field ∈ (Lp.simpleFunc ℝ (ENNReal.ofReal conjugate) measure :
      Set (Lp ℝ (ENNReal.ofReal conjugate) measure)),
      Tendsto (fun index => operators index field) filter (𝓝 (limitOperator field)) := by
    intro field simple
    let representative := Lp.simpleFunc.toSimpleFunc ⟨field, simple⟩
    have representativeMember : MemLp representative (ENNReal.ofReal conjugate) measure :=
      Lp.simpleFunc.memLp ⟨field, simple⟩
    have representativeTwo : MemLp representative 2 measure :=
      (SimpleFunc.memLp_iff_integrable (by norm_num) (by norm_num)).mpr
        ((SimpleFunc.memLp_iff_integrable
          (ENNReal.ofReal_pos.mpr conjugacy.symm.pos).ne' ENNReal.ofReal_ne_top).mp
            representativeMember)
    have equality : representativeMember.toLp representative = field :=
      congrArg (fun element : Lp.simpleFunc ℝ (ENNReal.ofReal conjugate) measure =>
        (element : Lp ℝ (ENNReal.ofReal conjugate) measure))
          (Lp.simpleFunc.toLp_toSimpleFunc ⟨field, simple⟩)
    have actual := weak representative representativeTwo
    have pairing (weight : Domain → ℝ)
        (weightMember : MemLp weight (ENNReal.ofReal exponent) measure) :
        integralSmulCLM conjugacy weightMember field =
          ∫ point, weight point * representative point ∂measure := by
      rw [← equality, integralSmulCLM_toLp]
      rfl
    simpa only [operators, limitOperator, pairing] using actual
  have result := ContinuousLinearMap.tendsto_apply_of_tendsto_on_dense
    (operators := operators) (limit := limitOperator)
    (Lp.simpleFunc.dense ENNReal.ofReal_ne_top)
    (fun index => (norm_integralSmulCLM_le conjugacy (members index)).trans (bounded index))
    converges (testMember.toLp test)
  simpa only [operators, limitOperator, integralSmulCLM_toLp, smul_eq_mul] using result

end MeasureTheory
