import EulerNonuniqueness.Section6.ScalarStraightening

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2

theorem separatrix_region_eventually : ∀ᶠ root in nhds (Real.sqrt 2 - 1),
    0 < root ∧ root < 1 ∧ 0 < root ^ 2 + 4 * root - 1 := by
  have rootPositive : 0 < Real.sqrt 2 - 1 := by linarith [sqrt_two_gt_one]
  have rootBelowOne : Real.sqrt 2 - 1 < 1 := by linarith [sqrt_two_lt_three_halves]
  have secondPositive : 0 < (Real.sqrt 2 - 1) ^ 2 + 4 * (Real.sqrt 2 - 1) - 1 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have polynomialContinuous : Continuous (fun root : ℝ => root ^ 2 + 4 * root - 1) := by fun_prop
  exact (eventually_gt_nhds rootPositive).and ((eventually_lt_nhds rootBelowOne).and
    (polynomialContinuous.continuousAt.eventually (eventually_gt_nhds secondPositive)))

theorem localNormalForm_on_separatrix_exists (frequency : ℝ) (frequencyNonzero : frequency ≠ 0) :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∀ᶠ unstable in nhds (0 : ℝ),
        (shapeChartVelocity frequency (unstable, graph unstable)).2 =
          deriv graph unstable * (shapeChartVelocity frequency (unstable, graph unstable)).1 ∧
        deriv coordinate unstable * (shapeChartVelocity frequency (unstable, graph unstable)).1 =
          2 * Real.sqrt 2 * frequency * coordinate unstable := by
  obtain ⟨graph, inverse, graphAnalytic, graphZero, graphDerivative, inverseAnalytic, inverseZero,
    graphIdentity, inverseIdentity⟩ := localSeparatrix_analytic_graph_exists
  have linearization := separatingLinearizedRoot_regular frequency frequencyNonzero
  have derivativeNonzero : 2 / (Real.sqrt 2 - 1) ≠ 0 := by
    exact div_ne_zero (by norm_num) (by linarith [sqrt_two_gt_one])
  have inverseDerivative : HasDerivAt inverse (2 / (Real.sqrt 2 - 1))⁻¹ 0 := by
    apply HasDerivAt.of_local_left_inverse inverseAnalytic.continuousAt
      (by simpa only [inverseZero] using separatingUnstableShape_hasDerivAt_rhombus)
      derivativeNonzero inverseIdentity
  let coordinate := fun unstable => (2 / (Real.sqrt 2 - 1)) *
    separatingLinearizedRoot frequency (inverse unstable)
  have inverseSmooth : ContDiffAt ℝ 2 inverse 0 := inverseAnalytic.contDiffAt
  have rootSmooth : ContDiffAt ℝ 2 (separatingLinearizedRoot frequency) (inverse 0) := by
    simpa only [inverseZero] using linearization.1
  have coordinateSmooth : ContDiffAt ℝ 2 coordinate 0 :=
    contDiffAt_const.mul (ContDiffAt.comp (f := inverse) (g := separatingLinearizedRoot frequency)
      0 rootSmooth inverseSmooth)
  have coordinateZero : coordinate 0 = 0 := by
    simp only [coordinate, inverseZero, separatingLinearizedRoot_zero, mul_zero]
  have rootDerivative : HasDerivAt (separatingLinearizedRoot frequency) 1 (inverse 0) := by
    simpa only [inverseZero] using linearization.2.1
  have coordinateDerivative : HasDerivAt coordinate 1 0 := by
    convert (rootDerivative.comp 0 inverseDerivative).const_mul (2 / (Real.sqrt 2 - 1)) using 1
    exact (mul_inv_cancel₀ derivativeNonzero).symm.trans (by ring)
  have inverseTendsto : Tendsto inverse (nhds (0 : ℝ)) (nhds (Real.sqrt 2 - 1)) := by
    simpa only [inverseZero] using inverseAnalytic.continuousAt.tendsto
  have graphEquality : (fun root => graph (separatingUnstableShape root)) =ᶠ[nhds (Real.sqrt 2 - 1)]
      separatingStableShape := graphIdentity.mono (fun _ identity => identity.2)
  have rightEquality : (fun unstable => separatingUnstableShape (inverse unstable)) =ᶠ[nhds (0 : ℝ)]
      (fun unstable => unstable) := inverseIdentity
  have inverseDifferentiable : ∀ᶠ unstable in nhds (0 : ℝ), DifferentiableAt ℝ inverse unstable :=
    ((inverseAnalytic.contDiffAt (n := 1)).eventually (by norm_num)).mono
      (fun _ smooth => smooth.differentiableAt (by norm_num))
  have graphDifferentiable : ∀ᶠ unstable in nhds (0 : ℝ), DifferentiableAt ℝ graph unstable :=
    ((graphAnalytic.contDiffAt (n := 1)).eventually (by norm_num)).mono
      (fun _ smooth => smooth.differentiableAt (by norm_num))
  have rootDifferentiable : ∀ᶠ root in nhds (Real.sqrt 2 - 1),
      DifferentiableAt ℝ (separatingLinearizedRoot frequency) root :=
    (linearization.1.eventually (by norm_num)).mono (fun _ smooth => smooth.differentiableAt (by norm_num))
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth,
    coordinateZero, coordinateDerivative, ?_⟩
  filter_upwards [inverseTendsto.eventually separatrix_region_eventually,
    inverseTendsto.eventually graphIdentity, inverseIdentity, inverseDifferentiable, graphDifferentiable,
    inverseTendsto.eventually rootDifferentiable, inverseTendsto.eventually linearization.2.2,
    inverseTendsto.eventually graphEquality.eventuallyEq_nhds, rightEquality.eventuallyEq_nhds] with
      unstable region graphIdentity inverseIdentity inverseDifferentiable graphDifferentiable
        rootDifferentiable scalarIdentity graphEquality rightEquality
  have derivatives := separatrix_shapes_differentiable region.1 region.2.1 region.2.2
  have unstableDerivative := derivatives.1.differentiableAt.hasDerivAt
  have stableDerivative := derivatives.2.differentiableAt.hasDerivAt
  have graphValue : graph unstable = separatingStableShape (inverse unstable) := by
    simpa only [inverseIdentity] using graphIdentity.2
  have graphAtRoot : HasDerivAt graph (deriv graph unstable) (separatingUnstableShape (inverse unstable)) := by
    simpa only [inverseIdentity] using graphDifferentiable.hasDerivAt
  have graphComposed := graphAtRoot.comp (inverse unstable) unstableDerivative
  have stableComposed := graphEquality.hasDerivAt_iff.mp graphComposed
  have graphDerivativeIdentity := stableComposed.unique stableDerivative
  have inverseComposed := unstableDerivative.comp unstable inverseDifferentiable.hasDerivAt
  have inverseDerivativeIdentity := (rightEquality.hasDerivAt_iff.mp inverseComposed).unique (hasDerivAt_id unstable)
  have fieldIdentity := separatrix_shape_velocity frequency region.1 region.2.1 region.2.2
  rw [inverseIdentity, ← graphValue] at fieldIdentity
  have firstField : (shapeChartVelocity frequency (unstable, graph unstable)).1 =
      separatingScalarVelocity frequency (inverse unstable) * deriv separatingUnstableShape (inverse unstable) :=
    congrArg Prod.fst fieldIdentity
  have secondField : (shapeChartVelocity frequency (unstable, graph unstable)).2 =
      separatingScalarVelocity frequency (inverse unstable) * deriv separatingStableShape (inverse unstable) :=
    congrArg Prod.snd fieldIdentity
  have coordinateAtPoint := (rootDifferentiable.hasDerivAt.comp unstable inverseDifferentiable.hasDerivAt).const_mul
    (2 / (Real.sqrt 2 - 1))
  have coordinateDerivativeIdentity : deriv coordinate unstable = (2 / (Real.sqrt 2 - 1)) *
      (deriv (separatingLinearizedRoot frequency) (inverse unstable) * deriv inverse unstable) :=
    coordinateAtPoint.deriv
  constructor
  · rw [firstField, secondField, ← graphDerivativeIdentity]
    ring
  · rw [coordinateDerivativeIdentity, firstField]
    change _ = 2 * Real.sqrt 2 * frequency *
      ((2 / (Real.sqrt 2 - 1)) * separatingLinearizedRoot frequency (inverse unstable))
    calc
      _ = (2 / (Real.sqrt 2 - 1)) *
          (deriv (separatingLinearizedRoot frequency) (inverse unstable) *
            separatingScalarVelocity frequency (inverse unstable)) *
          (deriv separatingUnstableShape (inverse unstable) * deriv inverse unstable) := by ring
      _ = _ := by rw [scalarIdentity, inverseDerivativeIdentity]; ring

end EulerNonuniqueness.Section6
