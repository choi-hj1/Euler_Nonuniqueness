import EulerNonuniqueness.Section6.LocalSeparatrix

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2

def separatrixCosine (root : ℝ) : ℝ := -(root ^ 2 + 2 * root - 1) / (2 * root)

def separatrixAngle (root : ℝ) : ℝ := 2 * Real.arccos (separatrixCosine root)

theorem separatrixCosine_complement {root : ℝ} (rootNonzero : root ≠ 0) :
    1 - separatrixCosine root ^ 2 =
      (1 - root ^ 2) * (root ^ 2 + 4 * root - 1) / (4 * root ^ 2) := by
  unfold separatrixCosine
  field_simp
  ring

theorem separatrixCosine_bounds {root : ℝ} (rootPositive : 0 < root) (belowOne : root < 1)
    (secondPositive : 0 < root ^ 2 + 4 * root - 1) :
    -1 < separatrixCosine root ∧ separatrixCosine root < 1 := by
  have firstPositive : 0 < 1 - root ^ 2 := by nlinarith
  have complementPositive : 0 < 1 - separatrixCosine root ^ 2 := by
    rw [separatrixCosine_complement rootPositive.ne']
    positivity
  constructor <;> nlinarith [sq_nonneg (separatrixCosine root + 1), sq_nonneg (separatrixCosine root - 1)]

theorem separatrixCosine_sqrt_complement {root : ℝ} (rootPositive : 0 < root) (belowOne : root < 1)
    (secondPositive : 0 < root ^ 2 + 4 * root - 1) :
    Real.sqrt (1 - separatrixCosine root ^ 2) =
      Real.sqrt (1 - root ^ 2) * Real.sqrt (root ^ 2 + 4 * root - 1) / (2 * root) := by
  have firstPositive : 0 < 1 - root ^ 2 := by nlinarith
  have denominator : Real.sqrt (4 * root ^ 2) = 2 * root := by
    rw [show 4 * root ^ 2 = (2 * root) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [separatrixCosine_complement rootPositive.ne', Real.sqrt_div
    (mul_nonneg firstPositive.le secondPositive.le), Real.sqrt_mul firstPositive.le, denominator]

theorem separatrixAngle_cos {root : ℝ} (rootPositive : 0 < root) (belowOne : root < 1)
    (secondPositive : 0 < root ^ 2 + 4 * root - 1) :
    Real.cos (separatrixAngle root) = 2 * separatrixCosine root ^ 2 - 1 := by
  have bounds := separatrixCosine_bounds rootPositive belowOne secondPositive
  rw [separatrixAngle, Real.cos_two_mul, Real.cos_arccos bounds.1.le bounds.2.le]

theorem separatrixAngle_sin {root : ℝ} (rootPositive : 0 < root) (belowOne : root < 1)
    (secondPositive : 0 < root ^ 2 + 4 * root - 1) :
    Real.sin (separatrixAngle root) =
      -(root ^ 2 + 2 * root - 1) * Real.sqrt (1 - root ^ 2) *
        Real.sqrt (root ^ 2 + 4 * root - 1) / (2 * root ^ 2) := by
  have bounds := separatrixCosine_bounds rootPositive belowOne secondPositive
  rw [separatrixAngle, Real.sin_two_mul, Real.cos_arccos bounds.1.le bounds.2.le,
    Real.sin_arccos, separatrixCosine_sqrt_complement rootPositive belowOne secondPositive]
  unfold separatrixCosine
  field_simp
  ring

theorem separatrixAngle_denominator {root : ℝ} (rootPositive : 0 < root) (belowOne : root < 1)
    (secondPositive : 0 < root ^ 2 + 4 * root - 1) :
    1 + (root ^ 2) ^ 2 - 2 * root ^ 2 * Real.cos (separatrixAngle root) =
      4 * root * (1 - root ^ 2) := by
  rw [separatrixAngle_cos rootPositive belowOne secondPositive]
  unfold separatrixCosine
  field_simp
  ring

theorem separatrix_radial_equation (frequency : ℝ) {root : ℝ}
    (rootPositive : 0 < root) (belowOne : root < 1)
    (secondPositive : 0 < root ^ 2 + 4 * root - 1) :
    radialVelocity frequency (root ^ 2) (separatrixAngle root) =
      2 * root * separatingScalarVelocity frequency root := by
  have firstPositive : 0 < 1 - root ^ 2 := by nlinarith
  unfold radialVelocity
  rw [separatrixAngle_denominator rootPositive belowOne secondPositive,
    separatrixAngle_sin rootPositive belowOne secondPositive]
  unfold separatingScalarVelocity
  have cube : Real.sqrt (1 - root ^ 2) ^ 3 = (1 - root ^ 2) * Real.sqrt (1 - root ^ 2) := by
    calc
      _ = Real.sqrt (1 - root ^ 2) ^ 2 * Real.sqrt (1 - root ^ 2) := by ring
      _ = _ := by rw [Real.sq_sqrt firstPositive.le]
  rw [cube]
  field_simp
  ring

theorem separatrixCosine_hasDerivAt {root : ℝ} (rootNonzero : root ≠ 0) :
    HasDerivAt separatrixCosine (-(root ^ 2 + 1) / (2 * root ^ 2)) root := by
  convert (((((hasDerivAt_id root).pow 2).add ((hasDerivAt_id root).const_mul 2)).sub_const 1).neg.div
    ((hasDerivAt_id root).const_mul 2) (mul_ne_zero (by norm_num) rootNonzero)) using 1
  simp only [id_eq, Nat.reduceSub, pow_one, mul_one]
  field_simp
  ring

theorem separatrixAngle_hasDerivAt {root : ℝ} (rootPositive : 0 < root) (belowOne : root < 1)
    (secondPositive : 0 < root ^ 2 + 4 * root - 1) :
    HasDerivAt separatrixAngle
      ((root ^ 2 + 1) / (root ^ 2 * Real.sqrt (1 - separatrixCosine root ^ 2))) root := by
  have bounds := separatrixCosine_bounds rootPositive belowOne secondPositive
  convert ((Real.hasDerivAt_arccos (ne_of_gt bounds.1) (ne_of_lt bounds.2)).comp root
    (separatrixCosine_hasDerivAt rootPositive.ne')).const_mul 2 using 1
  dsimp
  ring

theorem separatrixAngle_numerator {root : ℝ} (rootPositive : 0 < root) (belowOne : root < 1)
    (secondPositive : 0 < root ^ 2 + 4 * root - 1) :
    1 - 4 * root ^ 2 + (root ^ 2) ^ 2 + 2 * root ^ 2 * Real.cos (separatrixAngle root) =
      -2 * (1 - root ^ 2) * (root ^ 2 + 2 * root - 1) := by
  rw [separatrixAngle_cos rootPositive belowOne secondPositive]
  unfold separatrixCosine
  field_simp
  ring

theorem separatrix_angular_equation (frequency : ℝ) {root : ℝ}
    (rootPositive : 0 < root) (belowOne : root < 1)
    (secondPositive : 0 < root ^ 2 + 4 * root - 1) :
    shapeAngleVelocity frequency (root ^ 2) (separatrixAngle root) =
      ((root ^ 2 + 1) / (root ^ 2 * Real.sqrt (1 - separatrixCosine root ^ 2))) *
        separatingScalarVelocity frequency root := by
  have firstPositive : 0 < 1 - root ^ 2 := by nlinarith
  have firstSqrtNonzero : Real.sqrt (1 - root ^ 2) ≠ 0 := (Real.sqrt_pos.2 firstPositive).ne'
  have secondSqrtNonzero : Real.sqrt (root ^ 2 + 4 * root - 1) ≠ 0 := (Real.sqrt_pos.2 secondPositive).ne'
  unfold shapeAngleVelocity
  rw [separatrixAngle_denominator rootPositive belowOne secondPositive,
    separatrixAngle_numerator rootPositive belowOne secondPositive,
    separatrixCosine_sqrt_complement rootPositive belowOne secondPositive]
  unfold separatingScalarVelocity
  have cube : Real.sqrt (1 - root ^ 2) ^ 3 = (1 - root ^ 2) * Real.sqrt (1 - root ^ 2) := by
    calc
      _ = Real.sqrt (1 - root ^ 2) ^ 2 * Real.sqrt (1 - root ^ 2) := by ring
      _ = _ := by rw [Real.sq_sqrt firstPositive.le]
  rw [cube]
  field_simp [rootPositive.ne', firstPositive.ne', firstSqrtNonzero, secondSqrtNonzero]
  ring

theorem separatrix_shape_chart (root : ℝ) :
    shapeChart (root ^ 2) (separatrixAngle root) =
      (separatingUnstableShape root, separatingStableShape root) := by
  have rootNonzero : Real.sqrt 2 - 1 ≠ 0 := by linarith [sqrt_two_gt_one]
  have ratioIdentity : root ^ 2 / (Real.sqrt 2 - 1) ^ 2 - 1 =
      (root ^ 2 - (Real.sqrt 2 - 1) ^ 2) / (Real.sqrt 2 - 1) ^ 2 := by
    field_simp
  unfold shapeChart
  rw [rhombusRatio_square, ratioIdentity]
  rfl

theorem separatrix_shapes_differentiable {root : ℝ} (rootPositive : 0 < root) (belowOne : root < 1)
    (secondPositive : 0 < root ^ 2 + 4 * root - 1) :
    HasDerivAt separatingUnstableShape
      ((2 * root / (Real.sqrt 2 - 1) ^ 2 +
        ((root ^ 2 + 1) / (root ^ 2 * Real.sqrt (1 - separatrixCosine root ^ 2))) / Real.sqrt 2) / 2) root ∧
    HasDerivAt separatingStableShape
      ((2 * root / (Real.sqrt 2 - 1) ^ 2 -
        ((root ^ 2 + 1) / (root ^ 2 * Real.sqrt (1 - separatrixCosine root ^ 2))) / Real.sqrt 2) / 2) root := by
  have radial : HasDerivAt separatingRadialShape (2 * root / (Real.sqrt 2 - 1) ^ 2) root := by
    convert (((hasDerivAt_id root).pow 2).sub_const ((Real.sqrt 2 - 1) ^ 2)).div_const
      ((Real.sqrt 2 - 1) ^ 2) using 1
    simp
  have angular : HasDerivAt separatingAngularShape
      (((root ^ 2 + 1) / (root ^ 2 * Real.sqrt (1 - separatrixCosine root ^ 2))) / Real.sqrt 2) root :=
    ((separatrixAngle_hasDerivAt rootPositive belowOne secondPositive).sub_const Real.pi).div_const (Real.sqrt 2)
  exact ⟨(radial.add angular).div_const 2, (radial.sub angular).div_const 2⟩

theorem separatrix_shape_velocity (frequency : ℝ) {root : ℝ}
    (rootPositive : 0 < root) (belowOne : root < 1)
    (secondPositive : 0 < root ^ 2 + 4 * root - 1) :
    shapeChartVelocity frequency (separatingUnstableShape root, separatingStableShape root) =
      separatingScalarVelocity frequency root •
        (deriv separatingUnstableShape root, deriv separatingStableShape root) := by
  have derivatives := separatrix_shapes_differentiable rootPositive belowOne secondPositive
  rw [derivatives.1.deriv, derivatives.2.deriv, ← separatrix_shape_chart]
  unfold shapeChartVelocity
  rw [(shapeChart_reconstruction (root ^ 2) (separatrixAngle root)).1,
    (shapeChart_reconstruction (root ^ 2) (separatrixAngle root)).2,
    separatrix_radial_equation frequency rootPositive belowOne secondPositive,
    separatrix_angular_equation frequency rootPositive belowOne secondPositive, rhombusRatio_square]
  ext <;> dsimp <;> simp only [smul_eq_mul, div_eq_mul_inv] <;> ring

theorem localSeparatrix_invariant_graph_exists :
    ∃ graph : ℝ → ℝ, ContDiffAt ℝ 2 graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ∀ᶠ unstable in nhds (0 : ℝ), ∀ frequency : ℝ,
        (shapeChartVelocity frequency (unstable, graph unstable)).2 =
          deriv graph unstable * (shapeChartVelocity frequency (unstable, graph unstable)).1 := by
  obtain ⟨graph, inverse, graphSmooth, graphZero, graphDerivative, inverseSmooth, inverseZero,
    graphIdentity, inverseIdentity⟩ := localSeparatrix_graph_exists
  have rootPositive : 0 < Real.sqrt 2 - 1 := by linarith [sqrt_two_gt_one]
  have rootBelowOne : Real.sqrt 2 - 1 < 1 := by linarith [sqrt_two_lt_three_halves]
  have secondPositive : 0 < (Real.sqrt 2 - 1) ^ 2 + 4 * (Real.sqrt 2 - 1) - 1 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have polynomialContinuous : Continuous (fun root : ℝ => root ^ 2 + 4 * root - 1) := by fun_prop
  have polynomialPositive : ∀ᶠ root in nhds (Real.sqrt 2 - 1), 0 < root ^ 2 + 4 * root - 1 :=
    polynomialContinuous.continuousAt.eventually (eventually_gt_nhds secondPositive)
  have unstableZero : separatingUnstableShape (Real.sqrt 2 - 1) = 0 := by
    simp [separatingUnstableShape, separating_shapes_at_rhombus]
  have unstableTendsto : Tendsto separatingUnstableShape (nhds (Real.sqrt 2 - 1)) (nhds (0 : ℝ)) := by
    simpa only [unstableZero] using separating_shapes_contDiffAt_rhombus.1.continuousAt.tendsto
  have graphDifferentiable : ∀ᶠ root in nhds (Real.sqrt 2 - 1),
      DifferentiableAt ℝ graph (separatingUnstableShape root) :=
    unstableTendsto.eventually ((graphSmooth.eventually (by norm_num)).mono
      (fun _ smooth => smooth.differentiableAt (by norm_num)))
  have graphEquality : (fun root => graph (separatingUnstableShape root)) =ᶠ[nhds (Real.sqrt 2 - 1)]
      separatingStableShape := graphIdentity.mono (fun _ identity => identity.2)
  have rootTangency : ∀ᶠ root in nhds (Real.sqrt 2 - 1), ∀ frequency : ℝ,
      (shapeChartVelocity frequency (separatingUnstableShape root, separatingStableShape root)).2 =
        deriv graph (separatingUnstableShape root) *
          (shapeChartVelocity frequency (separatingUnstableShape root, separatingStableShape root)).1 := by
    filter_upwards [eventually_gt_nhds rootPositive, eventually_lt_nhds rootBelowOne,
      polynomialPositive, graphDifferentiable, graphEquality.eventuallyEq_nhds] with
        root rootPositive rootBelowOne polynomialPositive graphDifferentiable graphEquality
    have derivatives := separatrix_shapes_differentiable rootPositive rootBelowOne polynomialPositive
    have composed := graphDifferentiable.hasDerivAt.comp root derivatives.1
    have stableDerivative := graphEquality.hasDerivAt_iff.mp composed
    have derivativeEquality := stableDerivative.unique derivatives.2
    intro frequency
    rw [separatrix_shape_velocity frequency rootPositive rootBelowOne polynomialPositive]
    change separatingScalarVelocity frequency root * deriv separatingStableShape root =
      deriv graph (separatingUnstableShape root) *
        (separatingScalarVelocity frequency root * deriv separatingUnstableShape root)
    rw [derivatives.1.deriv, derivatives.2.deriv]
    nlinarith [congrArg (fun value : ℝ => separatingScalarVelocity frequency root * value) derivativeEquality]
  have inverseTendsto : Tendsto inverse (nhds (0 : ℝ)) (nhds (Real.sqrt 2 - 1)) := by
    simpa only [inverseZero] using inverseSmooth.continuousAt.tendsto
  refine ⟨graph, graphSmooth, graphZero, graphDerivative, ?_⟩
  filter_upwards [inverseTendsto.eventually rootTangency,
    inverseTendsto.eventually graphIdentity, inverseIdentity] with unstable tangency graphIdentity inverseIdentity
  intro frequency
  have graphValue : graph unstable = separatingStableShape (inverse unstable) := by
    simpa only [inverseIdentity] using graphIdentity.2
  simpa only [inverseIdentity, ← graphValue] using tangency frequency

end EulerNonuniqueness.Section6
