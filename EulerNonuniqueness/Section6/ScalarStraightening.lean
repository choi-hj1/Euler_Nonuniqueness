import EulerNonuniqueness.Section6.AnalyticSeparatrix

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2

theorem local_primitive_regular {integrand : ℝ → ℝ} {center : ℝ}
    (smooth : ContDiffAt ℝ 1 integrand center) :
    ContDiffAt ℝ 2 (fun endpoint => ∫ current in center..endpoint, integrand current) center ∧
      ∀ᶠ endpoint in nhds center,
        HasDerivAt (fun endpoint => ∫ current in center..endpoint, integrand current) (integrand endpoint) endpoint := by
  obtain ⟨radius, radiusPositive, ballInside⟩ := Metric.mem_nhds_iff.mp (smooth.eventually (by norm_num))
  have centerInside : center ∈ Metric.ball center radius := by simpa using radiusPositive
  have smoothOnBall : ∀ endpoint ∈ Metric.ball center radius, ContDiffAt ℝ 1 integrand endpoint :=
    fun _ endpointInside => ballInside endpointInside
  have continuousOnBall : ContinuousOn integrand (Metric.ball center radius) :=
    fun endpoint endpointInside => (smoothOnBall endpoint endpointInside).continuousAt.continuousWithinAt
  have derivative : ∀ endpoint ∈ Metric.ball center radius,
      HasDerivAt (fun endpoint => ∫ current in center..endpoint, integrand current) (integrand endpoint) endpoint := by
    intro endpoint endpointInside
    have intervalInside : uIcc center endpoint ⊆ Metric.ball center radius :=
      (convex_ball center radius).ordConnected.uIcc_subset centerInside endpointInside
    exact intervalIntegral.integral_hasDerivAt_right
      (continuousOnBall.mono intervalInside).intervalIntegrable
      (continuousOnBall.stronglyMeasurableAtFilter Metric.isOpen_ball endpoint endpointInside)
      (smoothOnBall endpoint endpointInside).continuousAt
  constructor
  · apply (contDiffAt_succ_iff_hasFDerivAt (n := 1)).mpr
    refine ⟨fun endpoint => integrand endpoint • (1 : ℝ →L[ℝ] ℝ),
      ⟨Metric.ball center radius, Metric.ball_mem_nhds center radiusPositive, ?_⟩,
      smooth.smul contDiffAt_const⟩
    intro endpoint endpointInside
    convert (derivative endpoint endpointInside).hasFDerivAt using 1
    apply ContinuousLinearMap.ext
    intro direction
    simp [smul_eq_mul, mul_comm]
  · exact mem_of_superset (Metric.ball_mem_nhds center radiusPositive) derivative

def separatingLinearizationPrimitive (frequency root : ℝ) : ℝ :=
  ∫ current in (Real.sqrt 2 - 1)..root, separatingLinearizationIntegrand frequency current

def separatingLinearizedRoot (frequency root : ℝ) : ℝ :=
  (root - (Real.sqrt 2 - 1)) * Real.exp (separatingLinearizationPrimitive frequency root)

theorem separatingLinearizedRoot_zero (frequency : ℝ) :
    separatingLinearizedRoot frequency (Real.sqrt 2 - 1) = 0 := by
  simp [separatingLinearizedRoot]

theorem separatingLinearizedRoot_regular (frequency : ℝ) (frequencyNonzero : frequency ≠ 0) :
    ContDiffAt ℝ 2 (separatingLinearizedRoot frequency) (Real.sqrt 2 - 1) ∧
      HasDerivAt (separatingLinearizedRoot frequency) 1 (Real.sqrt 2 - 1) ∧
      ∀ᶠ root in nhds (Real.sqrt 2 - 1),
        deriv (separatingLinearizedRoot frequency) root * separatingScalarVelocity frequency root =
          2 * Real.sqrt 2 * frequency * separatingLinearizedRoot frequency root := by
  have integrandAnalytic := separatingLinearizationIntegrand_analyticAt_rhombus frequency frequencyNonzero
  have primitiveRegular := local_primitive_regular (integrandAnalytic.contDiffAt (n := 1))
  have primitiveSmooth : ContDiffAt ℝ 2 (separatingLinearizationPrimitive frequency) (Real.sqrt 2 - 1) :=
    primitiveRegular.1
  have primitiveDerivative := primitiveRegular.2
  have transformSmooth : ContDiffAt ℝ 2 (separatingLinearizedRoot frequency) (Real.sqrt 2 - 1) :=
    (contDiffAt_id.sub contDiffAt_const).mul primitiveSmooth.exp
  have transformDerivative : ∀ᶠ root in nhds (Real.sqrt 2 - 1),
      HasDerivAt (separatingLinearizedRoot frequency)
        (Real.exp (separatingLinearizationPrimitive frequency root) *
          (1 + (root - (Real.sqrt 2 - 1)) * separatingLinearizationIntegrand frequency root)) root := by
    filter_upwards [primitiveDerivative] with root primitiveDerivative
    convert ((hasDerivAt_id root).sub_const (Real.sqrt 2 - 1)).mul primitiveDerivative.exp using 1
    simp only [id_eq, mul_one, separatingLinearizationPrimitive]
    ring
  have atRoot := transformDerivative.self_of_nhds
  have normalizedDerivative : HasDerivAt (separatingLinearizedRoot frequency) 1 (Real.sqrt 2 - 1) := by
    simpa [separatingLinearizationPrimitive] using atRoot
  refine ⟨transformSmooth, normalizedDerivative, ?_⟩
  have factorNonzeroAt : separatingScalarLinearFactor frequency (Real.sqrt 2 - 1) ≠ 0 := by
    rw [separatingScalarLinearFactor_at_rhombus]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne') frequencyNonzero
  have factorNonzero := (separatingScalarLinearFactor_analyticAt_rhombus frequency).continuousAt.eventually_ne factorNonzeroAt
  filter_upwards [transformDerivative, factorNonzero] with root transformDerivative factorNonzero
  rw [transformDerivative.deriv]
  have integrandIdentity := separatingLinearizationIntegrand_identity frequency root factorNonzero
  have scalarFactorization := separatingScalarVelocity_factorization frequency root
  unfold separatingLinearizedRoot
  linear_combination Real.exp (separatingLinearizationPrimitive frequency root) *
    (root - (Real.sqrt 2 - 1)) * integrandIdentity +
      Real.exp (separatingLinearizationPrimitive frequency root) * scalarFactorization

end EulerNonuniqueness.Section6
