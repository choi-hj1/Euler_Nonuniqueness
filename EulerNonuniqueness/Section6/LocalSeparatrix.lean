import EulerNonuniqueness.Section2.SeparatingReconstruction
import EulerNonuniqueness.Section6.NonlinearShape
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2

theorem separating_shapes_contDiffAt_rhombus :
    ContDiffAt ℝ 2 separatingUnstableShape (Real.sqrt 2 - 1) ∧
      ContDiffAt ℝ 2 separatingStableShape (Real.sqrt 2 - 1) := by
  have rootPositive : 0 < Real.sqrt 2 - 1 := by linarith [sqrt_two_gt_one]
  have polynomialZero : (Real.sqrt 2 - 1) ^ 2 + 2 * (Real.sqrt 2 - 1) - 1 = 0 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have innerValue : -((Real.sqrt 2 - 1) ^ 2 + 2 * (Real.sqrt 2 - 1) - 1) /
      (2 * (Real.sqrt 2 - 1)) = 0 := by rw [polynomialZero]; simp
  have radialSmooth : ContDiffAt ℝ 2 separatingRadialShape (Real.sqrt 2 - 1) := by
    unfold separatingRadialShape
    fun_prop (disch := positivity)
  have innerSmooth : ContDiffAt ℝ 2 (fun root : ℝ => -(root ^ 2 + 2 * root - 1) / (2 * root))
      (Real.sqrt 2 - 1) := by
    fun_prop (disch := positivity)
  have arccosSmooth : ContDiffAt ℝ 2 Real.arccos
      (-((Real.sqrt 2 - 1) ^ 2 + 2 * (Real.sqrt 2 - 1) - 1) / (2 * (Real.sqrt 2 - 1))) := by
    rw [innerValue]
    exact Real.contDiffAt_arccos (by norm_num) (by norm_num)
  have composed : ContDiffAt ℝ 2
      (fun root : ℝ => Real.arccos (-(root ^ 2 + 2 * root - 1) / (2 * root))) (Real.sqrt 2 - 1) :=
    ContDiffAt.comp (f := fun root : ℝ => -(root ^ 2 + 2 * root - 1) / (2 * root))
      (g := Real.arccos) (Real.sqrt 2 - 1) arccosSmooth innerSmooth
  have scaled : ContDiffAt ℝ 2
      (fun root : ℝ => 2 * Real.arccos (-(root ^ 2 + 2 * root - 1) / (2 * root))) (Real.sqrt 2 - 1) :=
    contDiffAt_const.mul composed
  have angularSmooth : ContDiffAt ℝ 2 separatingAngularShape (Real.sqrt 2 - 1) :=
    (scaled.sub contDiffAt_const).div_const (Real.sqrt 2)
  exact ⟨(radialSmooth.add angularSmooth).div_const 2,
    (radialSmooth.sub angularSmooth).div_const 2⟩

theorem localSeparatrix_graph_exists :
    ∃ graph inverse : ℝ → ℝ,
      ContDiffAt ℝ 2 graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 inverse 0 ∧ inverse 0 = Real.sqrt 2 - 1 ∧
      (∀ᶠ root in nhds (Real.sqrt 2 - 1),
        inverse (separatingUnstableShape root) = root ∧
          graph (separatingUnstableShape root) = separatingStableShape root) ∧
      (∀ᶠ unstable in nhds (0 : ℝ), separatingUnstableShape (inverse unstable) = unstable) := by
  have unstableSmooth := separating_shapes_contDiffAt_rhombus.1
  have stableSmooth := separating_shapes_contDiffAt_rhombus.2
  have unstableZero : separatingUnstableShape (Real.sqrt 2 - 1) = 0 := by
    simp [separatingUnstableShape, separating_shapes_at_rhombus]
  have stableZero : separatingStableShape (Real.sqrt 2 - 1) = 0 := by
    simp [separatingStableShape, separating_shapes_at_rhombus]
  have derivativeNonzero : 2 / (Real.sqrt 2 - 1) ≠ 0 := by
    exact div_ne_zero (by norm_num) (by linarith [sqrt_two_gt_one])
  have derivative := separatingUnstableShape_hasDerivAt_rhombus.hasFDerivAt_equiv derivativeNonzero
  let inverse := unstableSmooth.localInverse derivative (by norm_num)
  have inverseAtZero : inverse 0 = Real.sqrt 2 - 1 := by
    simpa only [unstableZero] using unstableSmooth.localInverse_apply_image derivative (by norm_num)
  have inverseSmooth : ContDiffAt ℝ 2 inverse 0 := by
    simpa only [unstableZero] using unstableSmooth.to_localInverse derivative (by norm_num)
  have strictDerivative := unstableSmooth.hasStrictFDerivAt' derivative (by norm_num)
  have leftInverse : ∀ᶠ root in nhds (Real.sqrt 2 - 1), inverse (separatingUnstableShape root) = root :=
    strictDerivative.eventually_left_inverse
  have rightInverse : ∀ᶠ unstable in nhds (0 : ℝ), separatingUnstableShape (inverse unstable) = unstable := by
    simpa only [unstableZero] using strictDerivative.eventually_right_inverse
  have inverseDerivative : HasDerivAt inverse (2 / (Real.sqrt 2 - 1))⁻¹ 0 := by
    apply HasDerivAt.of_local_left_inverse inverseSmooth.continuousAt
      (by simpa only [inverseAtZero] using separatingUnstableShape_hasDerivAt_rhombus)
      derivativeNonzero rightInverse
  let graph := fun unstable => separatingStableShape (inverse unstable)
  have graphSmooth : ContDiffAt ℝ 2 graph 0 := by
    have stableAtInverse : ContDiffAt ℝ 2 separatingStableShape (inverse 0) := by
      simpa only [inverseAtZero] using stableSmooth
    exact stableAtInverse.comp 0 inverseSmooth
  have graphDerivative : HasDerivAt graph 0 0 := by
    convert (show HasDerivAt separatingStableShape 0 (inverse 0) by
      simpa only [inverseAtZero] using separatingStableShape_hasDerivAt_rhombus).comp 0 inverseDerivative using 1
    simp
  refine ⟨graph, inverse, graphSmooth, ?_, graphDerivative, inverseSmooth, inverseAtZero, ?_, rightInverse⟩
  · change separatingStableShape (inverse 0) = 0
    rw [inverseAtZero, stableZero]
  · filter_upwards [leftInverse] with root inverseIdentity
    exact ⟨inverseIdentity, by change separatingStableShape (inverse (separatingUnstableShape root)) = _; rw [inverseIdentity]⟩

theorem localSeparatrix_quadratic_graph_exists :
    ∃ graph : ℝ → ℝ, ContDiffAt ℝ 2 graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      (∀ᶠ root in nhds (Real.sqrt 2 - 1), graph (separatingUnstableShape root) = separatingStableShape root) ∧
      ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ unstable : ℝ, |unstable| < radius →
        |graph unstable| ≤ bound * unstable ^ 2 := by
  obtain ⟨graph, inverse, graphSmooth, graphZero, graphDerivative, inverseSmooth, inverseZero,
      graphIdentity, inverseIdentity⟩ := localSeparatrix_graph_exists
  have fderivZero : fderiv ℝ graph 0 = 0 := by
    apply ContinuousLinearMap.ext
    intro point
    simpa using congrArg (fun derivative : ℝ →L[ℝ] ℝ => derivative point)
      graphDerivative.hasFDerivAt.fderiv
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    contDiffAt_quadratic_remainder graphSmooth
  refine ⟨graph, graphSmooth, graphZero, graphDerivative, graphIdentity.mono (fun _ identity => identity.2),
    bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro unstable unstableBound
  have result := estimate unstable (by simpa only [Real.norm_eq_abs] using unstableBound)
  simpa only [graphZero, sub_zero, fderivZero, ContinuousLinearMap.zero_apply, Real.norm_eq_abs, sq_abs] using result

end EulerNonuniqueness.Section6
