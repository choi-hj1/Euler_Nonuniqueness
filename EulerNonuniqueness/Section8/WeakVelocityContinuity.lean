import EulerNonuniqueness.General.WeakLpConvergence
import EulerNonuniqueness.Section8.VelocityCompactness

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem tendsto_integral_real_smul_complex_of_weakL2_uniform_memLp
    {Index : Type*} {filter : Filter Index} {sequence : Index → Vorticity}
    {limit : Vorticity} {exponent conjugate bound : ℝ}
    (conjugacy : exponent.HolderConjugate conjugate)
    (members : ∀ index, MemLp (sequence index) (ENNReal.ofReal exponent) volume)
    (limitMember : MemLp limit (ENNReal.ofReal exponent) volume)
    (bounded : ∀ index,
      (eLpNorm (sequence index) (ENNReal.ofReal exponent) volume).toReal ≤ bound)
    (weak : ∀ test : Vorticity, MemLp test 2 volume →
      Tendsto (fun index => ∫ point, sequence index point * test point) filter
        (𝓝 (∫ point, limit point * test point)))
    {test : Plane → Plane} (testMember : MemLp test (ENNReal.ofReal conjugate) volume) :
    Tendsto (fun index => ∫ point, sequence index point • test point) filter
      (𝓝 (∫ point, limit point • test point)) := by
  letI : ENNReal.HolderTriple (ENNReal.ofReal exponent) (ENNReal.ofReal conjugate) 1 :=
    by simpa using conjugacy.ennrealOfReal
  have pair (weight : Vorticity)
      (weightMember : MemLp weight (ENNReal.ofReal exponent) volume)
      (linear : Plane →L[ℝ] ℝ) :
      linear (∫ point, weight point • test point) =
        ∫ point, weight point * linear (test point) := by
    have integrable : Integrable (fun point => weight point • test point) :=
      memLp_one_iff_integrable.mp (testMember.smul weightMember)
    calc
      _ = ∫ point, linear (weight point • test point) :=
        (linear.integral_comp_comm integrable).symm
      _ = _ := by simp only [map_smul, smul_eq_mul]
  have coordinate (linear : Plane →L[ℝ] ℝ) :
      Tendsto (fun index => linear (∫ point, sequence index point • test point)) filter
        (𝓝 (linear (∫ point, limit point • test point))) := by
    have equality : (fun index => linear (∫ point, sequence index point • test point)) =
        (fun index => ∫ point, sequence index point * linear (test point)) :=
      funext fun index => pair (sequence index) (members index) linear
    rw [equality, pair limit limitMember linear]
    exact tendsto_integral_mul_of_weakL2_of_uniform_memLp conjugacy members limitMember
      bounded weak (linear.comp_memLp' testMember)
  have realConverges := coordinate Complex.reCLM
  have imaginaryConverges := coordinate Complex.imCLM
  have result := realConverges.ofReal.add (imaginaryConverges.ofReal.mul_const Complex.I)
  simpa only [Complex.reCLM_apply, Complex.imCLM_apply, Complex.re_add_im] using result

theorem tendsto_biotSavart_of_weakL2_uniform_memLp_support
    {Index : Type*} {filter : Filter Index} {sequence : Index → Vorticity}
    {limit : Vorticity} {exponent conjugate radius bound : ℝ}
    (conjugacy : exponent.HolderConjugate conjugate)
    (conjugateBound : conjugate < 2) (radiusNonnegative : 0 ≤ radius)
    (members : ∀ index, MemLp (sequence index) (ENNReal.ofReal exponent) volume)
    (limitMember : MemLp limit (ENNReal.ofReal exponent) volume)
    (supported : ∀ index, Function.support (sequence index) ⊆ Metric.closedBall 0 radius)
    (limitSupported : Function.support limit ⊆ Metric.closedBall 0 radius)
    (bounded : ∀ index,
      (eLpNorm (sequence index) (ENNReal.ofReal exponent) volume).toReal ≤ bound)
    (weak : ∀ test : Vorticity, MemLp test 2 volume →
      Tendsto (fun index => ∫ point, sequence index point * test point) filter
        (𝓝 (∫ point, limit point * test point))) (position : Plane) :
    Tendsto (fun index => biotSavart (sequence index) position) filter
      (𝓝 (biotSavart limit position)) := by
  let truncated := (Metric.ball 0 (‖position‖ + radius + 1)).indicator biotSavartKernel
  have truncatedMember : MemLp truncated (ENNReal.ofReal conjugate) volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr
      (memLp_biotSavartKernel_ball conjugacy.symm.pos conjugateBound (by positivity))
  let test : Plane → Plane := fun source => truncated (position - source)
  have testMember : MemLp test (ENNReal.ofReal conjugate) volume :=
    truncatedMember.comp_measurePreserving (volume.measurePreserving_sub_left position)
  have equality (weight : Vorticity)
      (weightSupported : Function.support weight ⊆ Metric.closedBall 0 radius) :
      biotSavart weight position = ∫ source, weight source • test source := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun source =>
      (biotSavart_integrand_eq_truncated weightSupported
        (show ‖position‖ + radius < ‖position‖ + radius + 1 by linarith) source).symm
  simp_rw [equality _ (supported _), equality _ limitSupported]
  exact tendsto_integral_real_smul_complex_of_weakL2_uniform_memLp
    conjugacy members limitMember bounded weak testMember

theorem LocalCompactnessHypotheses.continuousInLp_biotSavart
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) (index : ℕ) :
    ContinuousInLpOn horizon 2 (fun time => biotSavart (sequence index time)) := by
  let members : ∀ time : Icc (0 : ℝ) horizon,
      MemLp (biotSavart (sequence index time)) 2 volume :=
    fun time => hypotheses.biotSavart_memLp_two index time.property
  refine ⟨by norm_num, members, ?_⟩
  apply continuous_iff_seqContinuous.mpr
  intro times time timeConverges
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun step => members (times step))
    _ (members time)).mpr
  obtain ⟨radius, radiusPositive, supported⟩ := hypotheses.2.1
  obtain ⟨normBound, normBoundFinite, normBounded⟩ :=
    hypotheses.uniform_eLpNorm_bound horizonNonnegative (by norm_num : (1 : ℝ) ≤ 4)
  have weak (test : Vorticity) (testMember : MemLp test 2 volume) :
      Tendsto (fun step => ∫ point, sequence index (times step) point * test point) atTop
        (𝓝 (∫ point, sequence index time point * test point)) :=
    (((hypotheses.2.2 index).2.1.2 test testMember).tendsto time).comp timeConverges
  have pointwise (position : Plane) : Tendsto
      (fun step => biotSavart (sequence index (times step)) position) atTop
      (𝓝 (biotSavart (sequence index time) position)) := by
    apply tendsto_biotSavart_of_weakL2_uniform_memLp_support
      holderConjugate_four_fourThirds (by norm_num) radiusPositive.le
      (fun step => ((hypotheses.2.2 index).2.2.2 4 (by norm_num)
        (times step) (times step).property).1)
      (((hypotheses.2.2 index).2.2.2 4 (by norm_num) time time.property).1)
      (fun step => supported index (times step) (times step).property)
      (supported index time time.property) (bound := normBound.toReal)
    · intro step
      exact ENNReal.toReal_mono normBoundFinite.ne
        (normBounded index (times step) (times step).property)
    · exact weak
  obtain ⟨bound, boundMember, bounded⟩ := hypotheses.biotSavart_L2_dominator horizonNonnegative
  exact tendsto_eLpNorm_of_dominated_convergence (by norm_num) (by norm_num)
    (fun step => (hypotheses.continuous_biotSavart index (times step).property).aestronglyMeasurable)
    boundMember
    (fun step => Filter.Eventually.of_forall (bounded index (times step) (times step).property))
    (Filter.Eventually.of_forall pointwise)

end EulerNonuniqueness
