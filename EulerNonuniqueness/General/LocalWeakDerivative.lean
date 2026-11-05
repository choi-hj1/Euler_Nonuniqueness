import EulerNonuniqueness.General.IntervalPrimitive
import EulerNonuniqueness.General.WeakDerivative

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

theorem Continuous.eq_constOn_Ioo_of_integral_mul_deriv_eq_zero {function : ℝ → ℝ}
    {lower upper : ℝ} (continuous : Continuous function) (ordered : lower < upper)
    (weak : ∀ test : ℝ → ℝ, ContDiff ℝ ∞ test → HasCompactSupport test →
      tsupport test ⊆ Ioo lower upper → (∫ point, function point * deriv test point) = 0) :
    ∃ constant : ℝ, ∀ point ∈ Ioo lower upper, function point = constant := by
  let center := (lower + upper) / 2
  let bump : ContDiffBump center :=
    ⟨(upper - lower) / 8, (upper - lower) / 4, by linarith, by linarith⟩
  let reference := bump.normed volume
  have referenceSmooth : ContDiff ℝ ∞ reference := bump.contDiff_normed
  have referenceCompact : HasCompactSupport reference := bump.hasCompactSupport_normed
  have referenceIntegral : (∫ point, reference point) = 1 := bump.integral_normed
  have referenceIntegrable : Integrable reference := bump.integrable_normed
  have referenceSupport : tsupport reference ⊆ Ioo lower upper := by
    intro point inside
    rw [bump.tsupport_normed_eq] at inside
    have distanceBound : |point - center| ≤ (upper - lower) / 4 := by
      simpa only [Metric.mem_closedBall, Real.dist_eq, bump] using inside
    rcases abs_le.mp distanceBound with ⟨leftBound, rightBound⟩
    dsimp [center] at leftBound rightBound
    constructor <;> linarith
  have referenceProduct : Integrable (fun point => reference point * function point) :=
    (referenceSmooth.continuous.mul continuous).integrable_of_hasCompactSupport
      referenceCompact.mul_right
  let constant := ∫ point, reference point * function point
  have testIdentity (test : ℝ → ℝ) (smooth : ContDiff ℝ ∞ test)
      (compact : HasCompactSupport test) (contained : tsupport test ⊆ Ioo lower upper) :
      (∫ point, test point * function point) = (∫ point, test point) * constant := by
    let mass := ∫ point, test point
    let centered := fun point => test point - mass * reference point
    have centeredSmooth : ContDiff ℝ ∞ centered :=
      smooth.sub (contDiff_const.mul referenceSmooth)
    have centeredCompact : HasCompactSupport centered :=
      compact.comp₂_left (m := fun first second : ℝ => first - second)
        referenceCompact.mul_left (sub_self (0 : ℝ))
    have centeredSupport : tsupport centered ⊆ Ioo lower upper := by
      have supportUnion : tsupport centered ⊆ tsupport test ∪ tsupport reference := by
        apply closure_minimal _ ((isClosed_tsupport test).union (isClosed_tsupport reference))
        intro point nonzero
        by_cases testZero : test point = 0
        · apply Or.inr
          apply subset_tsupport reference
          intro referenceZero
          exact nonzero (by dsimp [centered]; rw [testZero, referenceZero]; ring)
        · exact Or.inl (subset_tsupport test testZero)
      exact supportUnion.trans (union_subset contained referenceSupport)
    have centeredIntegral : (∫ point, centered point) = 0 := by
      dsimp only [centered]
      rw [integral_sub (smooth.continuous.integrable_of_hasCompactSupport compact)
        (referenceIntegrable.const_mul mass), integral_const_mul, referenceIntegral]
      dsimp [mass]
      ring
    obtain ⟨primitive, primitiveSmooth, primitiveCompact, primitiveSupport, derivative⟩ :=
      exists_contDiff_compact_primitive_supportedIn centeredSmooth centeredCompact ordered
        centeredSupport centeredIntegral
    have derivativeEquality : deriv primitive = centered :=
      funext fun point => (derivative point).deriv
    have zero := weak primitive primitiveSmooth primitiveCompact primitiveSupport
    rw [derivativeEquality] at zero
    have productIntegrable : Integrable (fun point => test point * function point) :=
      (smooth.continuous.mul continuous).integrable_of_hasCompactSupport compact.mul_right
    have identity : (∫ point, function point * centered point) =
        (∫ point, test point * function point) - mass * constant := by
      calc
        _ = ∫ point, test point * function point - mass * (reference point * function point) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun point => by dsimp [centered]; ring
        _ = _ := by rw [integral_sub productIntegrable (referenceProduct.const_mul mass),
          integral_const_mul]
    rw [identity] at zero
    exact sub_eq_zero.mp zero
  have vanishes : ∀ᵐ point ∂(volume : Measure ℝ),
      point ∈ Ioo lower upper → function point - constant = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((continuous.sub continuous_const).locallyIntegrable.locallyIntegrableOn _)
    intro test smooth compact contained
    have testIntegrable := smooth.continuous.integrable_of_hasCompactSupport compact (μ := volume)
    have productIntegrable := (smooth.continuous.mul continuous).integrable_of_hasCompactSupport
      compact.mul_right (μ := volume)
    simp only [smul_eq_mul, mul_sub]
    rw [integral_sub productIntegrable (testIntegrable.mul_const constant), integral_mul_const,
      testIdentity test smooth compact contained]
    ring
  have equal : function =ᵐ[volume.restrict (Ioo lower upper)] (fun _ => constant) := by
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    exact vanishes.mono fun point equality inside => sub_eq_zero.mp (equality inside)
  exact ⟨constant, MeasureTheory.Measure.eqOn_open_of_ae_eq equal isOpen_Ioo
    continuous.continuousOn continuous_const.continuousOn⟩

theorem Continuous.sub_eq_intervalIntegral_of_weak_derivative_on_Icc
    {function source : ℝ → ℝ} {lower upper : ℝ}
    (continuous : Continuous function) (sourceContinuous : Continuous source)
    (ordered : lower < upper)
    (weak : ∀ test : ℝ → ℝ, ContDiff ℝ ∞ test → HasCompactSupport test →
      tsupport test ⊆ Ioo lower upper →
      (∫ point, function point * deriv test point) = -(∫ point, source point * test point))
    {first second : ℝ} (firstInside : first ∈ Icc lower upper)
    (secondInside : second ∈ Icc lower upper) :
    function second - function first = ∫ point in first..second, source point := by
  let primitive : ℝ → ℝ := fun point => ∫ parameter in (0 : ℝ)..point, source parameter
  have derivative (point : ℝ) : HasDerivAt primitive (source point) point :=
    intervalIntegral.integral_hasDerivAt_right (sourceContinuous.intervalIntegrable 0 point)
      sourceContinuous.stronglyMeasurable.stronglyMeasurableAtFilter sourceContinuous.continuousAt
  have primitiveContinuous : Continuous primitive :=
    continuous_iff_continuousAt.mpr fun point => (derivative point).continuousAt
  obtain ⟨constant, constantProperty⟩ :=
    (continuous.sub primitiveContinuous).eq_constOn_Ioo_of_integral_mul_deriv_eq_zero ordered
      (fun test smooth compact contained => by
        have testDerivativeContinuous : Continuous (deriv test) :=
          smooth.continuous_deriv (by simp)
        have testDerivativeCompact : HasCompactSupport (deriv test) := compact.deriv
        have primitiveIdentity := integral_mul_deriv_eq_deriv_mul_of_integrable
          derivative (fun point => (smooth.differentiable (by simp) point).hasDerivAt)
          ((primitiveContinuous.mul testDerivativeContinuous).integrable_of_hasCompactSupport
            testDerivativeCompact.mul_left)
          ((sourceContinuous.mul smooth.continuous).integrable_of_hasCompactSupport compact.mul_left)
          ((primitiveContinuous.mul smooth.continuous).integrable_of_hasCompactSupport compact.mul_left)
        have functionProduct :=
          (continuous.mul testDerivativeContinuous).integrable_of_hasCompactSupport
            testDerivativeCompact.mul_left (μ := volume)
        have primitiveProduct :=
          (primitiveContinuous.mul testDerivativeContinuous).integrable_of_hasCompactSupport
            testDerivativeCompact.mul_left (μ := volume)
        simp only [Pi.sub_apply, sub_mul]
        rw [integral_sub functionProduct primitiveProduct, weak test smooth compact contained,
          primitiveIdentity]
        ring)
  have closed : IsClosed {point : ℝ | function point - primitive point = constant} :=
    isClosed_eq (continuous.sub primitiveContinuous) continuous_const
  have closureAgreement : Icc lower upper ⊆ {point : ℝ | function point - primitive point = constant} := by
    rw [← closure_Ioo ordered.ne]
    exact closure_minimal constantProperty closed
  have firstEquality := closureAgreement firstInside
  have secondEquality := closureAgreement secondInside
  have additive := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (sourceContinuous.intervalIntegrable 0 first) (sourceContinuous.intervalIntegrable first second)
  change function first - primitive first = constant at firstEquality
  change function second - primitive second = constant at secondEquality
  dsimp only [primitive] at firstEquality secondEquality
  linarith

theorem Continuous.norm_sub_le_of_weak_derivative_bound
    {function source : ℝ → ℝ} {lower upper bound : ℝ}
    (continuous : Continuous function) (sourceContinuous : Continuous source)
    (ordered : lower < upper)
    (weak : ∀ test : ℝ → ℝ, ContDiff ℝ ∞ test → HasCompactSupport test →
      tsupport test ⊆ Ioo lower upper →
      (∫ point, function point * deriv test point) = -(∫ point, source point * test point))
    (bounded : ∀ point ∈ Icc lower upper, ‖source point‖ ≤ bound)
    {first second : ℝ} (firstInside : first ∈ Icc lower upper)
    (secondInside : second ∈ Icc lower upper) :
    ‖function second - function first‖ ≤ bound * |second - first| := by
  rw [continuous.sub_eq_intervalIntegral_of_weak_derivative_on_Icc
    sourceContinuous ordered weak firstInside secondInside]
  exact intervalIntegral.norm_integral_le_of_norm_le_const fun point inside =>
    bounded point (uIcc_subset_Icc firstInside secondInside (uIoc_subset_uIcc inside))
