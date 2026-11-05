import EulerNonuniqueness.Section6.SeparatrixDynamics
import Mathlib.Analysis.Analytic.IsolatedZeros

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace EulerNonuniqueness.Section6

attribute [local fun_prop] ContDiffAt.sqrt

open EulerNonuniqueness.Section2

theorem separating_shapes_analyticAt_rhombus :
    AnalyticAt ℝ separatingUnstableShape (Real.sqrt 2 - 1) ∧
      AnalyticAt ℝ separatingStableShape (Real.sqrt 2 - 1) := by
  have rootPositive : 0 < Real.sqrt 2 - 1 := by linarith [sqrt_two_gt_one]
  have polynomialZero : (Real.sqrt 2 - 1) ^ 2 + 2 * (Real.sqrt 2 - 1) - 1 = 0 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have innerValue : -((Real.sqrt 2 - 1) ^ 2 + 2 * (Real.sqrt 2 - 1) - 1) /
      (2 * (Real.sqrt 2 - 1)) = 0 := by rw [polynomialZero]; simp
  have radialAnalyticOrder : ContDiffAt ℝ ω separatingRadialShape (Real.sqrt 2 - 1) := by
    unfold separatingRadialShape
    fun_prop (disch := positivity)
  have innerAnalyticOrder : ContDiffAt ℝ ω (fun root : ℝ => -(root ^ 2 + 2 * root - 1) / (2 * root))
      (Real.sqrt 2 - 1) := by
    fun_prop (disch := positivity)
  have arccosAnalyticOrder : ContDiffAt ℝ ω Real.arccos
      (-((Real.sqrt 2 - 1) ^ 2 + 2 * (Real.sqrt 2 - 1) - 1) / (2 * (Real.sqrt 2 - 1))) := by
    rw [innerValue]
    exact Real.contDiffAt_arccos (by norm_num) (by norm_num)
  have composed : ContDiffAt ℝ ω
      (fun root : ℝ => Real.arccos (-(root ^ 2 + 2 * root - 1) / (2 * root))) (Real.sqrt 2 - 1) :=
    ContDiffAt.comp (f := fun root : ℝ => -(root ^ 2 + 2 * root - 1) / (2 * root))
      (g := Real.arccos) (Real.sqrt 2 - 1) arccosAnalyticOrder innerAnalyticOrder
  have scaled : ContDiffAt ℝ ω
      (fun root : ℝ => 2 * Real.arccos (-(root ^ 2 + 2 * root - 1) / (2 * root))) (Real.sqrt 2 - 1) :=
    contDiffAt_const.mul composed
  have angularAnalyticOrder : ContDiffAt ℝ ω separatingAngularShape (Real.sqrt 2 - 1) :=
    (scaled.sub contDiffAt_const).div_const (Real.sqrt 2)
  exact ⟨((radialAnalyticOrder.add angularAnalyticOrder).div_const 2).analyticAt,
    ((radialAnalyticOrder.sub angularAnalyticOrder).div_const 2).analyticAt⟩

theorem localSeparatrix_analytic_graph_exists :
    ∃ graph inverse : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      AnalyticAt ℝ inverse 0 ∧ inverse 0 = Real.sqrt 2 - 1 ∧
      (∀ᶠ root in nhds (Real.sqrt 2 - 1),
        inverse (separatingUnstableShape root) = root ∧
          graph (separatingUnstableShape root) = separatingStableShape root) ∧
      (∀ᶠ unstable in nhds (0 : ℝ), separatingUnstableShape (inverse unstable) = unstable) := by
  obtain ⟨graph, inverse, graphSmooth, graphZero, graphDerivative, inverseSmooth, inverseZero,
    graphIdentity, inverseIdentity⟩ := localSeparatrix_graph_exists
  have unstableAnalytic := separating_shapes_analyticAt_rhombus.1
  have stableAnalytic := separating_shapes_analyticAt_rhombus.2
  have unstableZero : separatingUnstableShape (Real.sqrt 2 - 1) = 0 := by
    simp [separatingUnstableShape, separating_shapes_at_rhombus]
  have derivativeNonzero : 2 / (Real.sqrt 2 - 1) ≠ 0 := by
    exact div_ne_zero (by norm_num) (by linarith [sqrt_two_gt_one])
  have derivative := separatingUnstableShape_hasDerivAt_rhombus.hasFDerivAt_equiv derivativeNonzero
  have analyticOrder : ContDiffAt ℝ ω separatingUnstableShape (Real.sqrt 2 - 1) := unstableAnalytic.contDiffAt
  let analyticInverse := analyticOrder.localInverse derivative (by simp)
  have analyticInverseZero : analyticInverse 0 = Real.sqrt 2 - 1 := by
    simpa only [unstableZero] using analyticOrder.localInverse_apply_image derivative (by simp)
  have analyticInverseAnalytic : AnalyticAt ℝ analyticInverse 0 := by
    apply ContDiffAt.analyticAt
    simpa only [unstableZero] using analyticOrder.to_localInverse derivative (by simp)
  have strictDerivative := analyticOrder.hasStrictFDerivAt' derivative (by simp)
  have analyticRightInverse : ∀ᶠ unstable in nhds (0 : ℝ),
      separatingUnstableShape (analyticInverse unstable) = unstable := by
    simpa only [unstableZero] using strictDerivative.eventually_right_inverse
  have analyticInverseTendsto : Tendsto analyticInverse (nhds (0 : ℝ)) (nhds (Real.sqrt 2 - 1)) := by
    simpa only [analyticInverseZero] using analyticInverseAnalytic.continuousAt.tendsto
  have inverseEquality : analyticInverse =ᶠ[nhds (0 : ℝ)] inverse := by
    filter_upwards [analyticInverseTendsto.eventually graphIdentity, analyticRightInverse] with
      unstable leftInverse rightInverse
    simpa only [rightInverse] using leftInverse.1.symm
  have inverseAnalytic := analyticInverseAnalytic.congr inverseEquality
  have inverseTendsto : Tendsto inverse (nhds (0 : ℝ)) (nhds (Real.sqrt 2 - 1)) := by
    simpa only [inverseZero] using inverseAnalytic.continuousAt.tendsto
  have graphEquality : (fun unstable => separatingStableShape (inverse unstable)) =ᶠ[nhds (0 : ℝ)] graph := by
    filter_upwards [inverseTendsto.eventually graphIdentity, inverseIdentity] with unstable graphIdentity inverseIdentity
    simpa only [inverseIdentity] using graphIdentity.2.symm
  have stableAtInverse : AnalyticAt ℝ separatingStableShape (inverse 0) := by
    simpa only [inverseZero] using stableAnalytic
  have graphAnalytic := (stableAtInverse.comp inverseAnalytic).congr graphEquality
  exact ⟨graph, inverse, graphAnalytic, graphZero, graphDerivative, inverseAnalytic, inverseZero,
    graphIdentity, inverseIdentity⟩

theorem separatingScalarLinearFactor_analyticAt_rhombus (frequency : ℝ) :
    AnalyticAt ℝ (separatingScalarLinearFactor frequency) (Real.sqrt 2 - 1) := by
  have rootPositive : 0 < Real.sqrt 2 - 1 := by linarith [sqrt_two_gt_one]
  have firstPositive : 0 < 1 - (Real.sqrt 2 - 1) ^ 2 := by
    nlinarith [sqrt_two_lt_three_halves, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have secondPositive : 0 < (Real.sqrt 2 - 1) ^ 2 + 4 * (Real.sqrt 2 - 1) - 1 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  apply ContDiffAt.analyticAt
  unfold separatingScalarLinearFactor
  fun_prop (disch := positivity)

def separatingLinearizationIntegrand (frequency root : ℝ) : ℝ :=
  -dslope (separatingScalarLinearFactor frequency) (Real.sqrt 2 - 1) root /
    separatingScalarLinearFactor frequency root

theorem separatingLinearizationIntegrand_analyticAt_rhombus (frequency : ℝ)
    (frequencyNonzero : frequency ≠ 0) :
    AnalyticAt ℝ (separatingLinearizationIntegrand frequency) (Real.sqrt 2 - 1) := by
  have factorAnalytic := separatingScalarLinearFactor_analyticAt_rhombus frequency
  obtain ⟨series, seriesProperty⟩ := factorAnalytic
  have slopeAnalytic : AnalyticAt ℝ (dslope (separatingScalarLinearFactor frequency) (Real.sqrt 2 - 1))
      (Real.sqrt 2 - 1) := ⟨series.fslope, seriesProperty.has_fpower_series_dslope_fslope⟩
  have factorNonzero : separatingScalarLinearFactor frequency (Real.sqrt 2 - 1) ≠ 0 := by
    rw [separatingScalarLinearFactor_at_rhombus]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne')
      frequencyNonzero
  exact slopeAnalytic.neg.div ⟨series, seriesProperty⟩ factorNonzero

theorem separatingLinearizationIntegrand_identity (frequency root : ℝ)
    (factorNonzero : separatingScalarLinearFactor frequency root ≠ 0) :
    separatingLinearizationIntegrand frequency root * separatingScalarVelocity frequency root =
      2 * Real.sqrt 2 * frequency - separatingScalarLinearFactor frequency root := by
  have slopeIdentity := sub_smul_dslope (separatingScalarLinearFactor frequency) (Real.sqrt 2 - 1) root
  rw [smul_eq_mul, separatingScalarLinearFactor_at_rhombus] at slopeIdentity
  unfold separatingLinearizationIntegrand
  rw [separatingScalarVelocity_factorization]
  field_simp
  linear_combination -separatingScalarLinearFactor frequency root * slopeIdentity

end EulerNonuniqueness.Section6
