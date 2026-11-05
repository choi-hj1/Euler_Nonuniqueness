import EulerNonuniqueness.General.CompactPrimitive

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

theorem Continuous.eq_const_of_integral_mul_deriv_eq_zero {function : ℝ → ℝ}
    (continuous : Continuous function)
    (weak : ∀ test : ℝ → ℝ, ContDiff ℝ ∞ test → HasCompactSupport test →
      (∫ point, function point * deriv test point) = 0) :
    ∀ first second, function first = function second := by
  let bump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let reference := bump.normed volume
  have referenceSmooth : ContDiff ℝ ∞ reference := bump.contDiff_normed
  have referenceCompact : HasCompactSupport reference := bump.hasCompactSupport_normed
  have referenceIntegral : (∫ point, reference point) = 1 := bump.integral_normed
  have referenceIntegrable : Integrable reference := bump.integrable_normed
  have referenceProduct : Integrable (fun point => reference point * function point) :=
    (referenceSmooth.continuous.mul continuous).integrable_of_hasCompactSupport
      referenceCompact.mul_right
  let constant := ∫ point, reference point * function point
  have testIdentity (test : ℝ → ℝ) (smooth : ContDiff ℝ ∞ test)
      (compact : HasCompactSupport test) :
      (∫ point, test point * function point) = (∫ point, test point) * constant := by
    let mass := ∫ point, test point
    let centered := fun point => test point - mass * reference point
    have centeredSmooth : ContDiff ℝ ∞ centered :=
      smooth.sub (contDiff_const.mul referenceSmooth)
    have centeredCompact : HasCompactSupport centered :=
      compact.comp₂_left (m := fun first second : ℝ => first - second)
        referenceCompact.mul_left (sub_self (0 : ℝ))
    have centeredIntegral : (∫ point, centered point) = 0 := by
      dsimp only [centered]
      rw [integral_sub (smooth.continuous.integrable_of_hasCompactSupport compact)
        (referenceIntegrable.const_mul mass), integral_const_mul, referenceIntegral]
      dsimp [mass]
      ring
    obtain ⟨primitive, primitiveSmooth, primitiveCompact, derivative⟩ :=
      exists_contDiff_compact_primitive centeredSmooth centeredCompact centeredIntegral
    have derivativeEquality : deriv primitive = centered :=
      funext fun point => (derivative point).deriv
    have zero := weak primitive primitiveSmooth primitiveCompact
    rw [derivativeEquality] at zero
    have productIntegrable : Integrable (fun point => test point * function point) :=
      (smooth.continuous.mul continuous).integrable_of_hasCompactSupport compact.mul_right
    have identity : (∫ point, function point * centered point) =
        (∫ point, test point * function point) - mass * constant := by
      calc
        _ = ∫ point, test point * function point -
            mass * (reference point * function point) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun point => by dsimp [centered]; ring
        _ = _ := by rw [integral_sub productIntegrable (referenceProduct.const_mul mass),
          integral_const_mul]
    rw [identity] at zero
    exact sub_eq_zero.mp zero
  have vanishes : ∀ᵐ point ∂(volume : Measure ℝ), function point - constant = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (continuous.sub continuous_const).locallyIntegrable
    intro test smooth compact
    have testIntegrable := smooth.continuous.integrable_of_hasCompactSupport compact (μ := volume)
    have productIntegrable := (smooth.continuous.mul continuous).integrable_of_hasCompactSupport
      compact.mul_right (μ := volume)
    simp only [smul_eq_mul, mul_sub]
    rw [integral_sub productIntegrable (testIntegrable.mul_const constant),
      integral_mul_const, testIdentity test smooth compact]
    ring
  have equal : function = fun _ => constant := MeasureTheory.Measure.eq_of_ae_eq
    (vanishes.mono fun _ equality => sub_eq_zero.mp equality) continuous continuous_const
  intro first second
  rw [congrFun equal first, congrFun equal second]

theorem Continuous.sub_eq_intervalIntegral_of_weak_derivative {function source : ℝ → ℝ}
    (continuous : Continuous function) (sourceContinuous : Continuous source)
    (weak : ∀ test : ℝ → ℝ, ContDiff ℝ ∞ test → HasCompactSupport test →
      (∫ point, function point * deriv test point) = -(∫ point, source point * test point))
    (first second : ℝ) :
    function second - function first = ∫ point in first..second, source point := by
  let primitive : ℝ → ℝ := fun point => ∫ parameter in (0 : ℝ)..point, source parameter
  have derivative (point : ℝ) : HasDerivAt primitive (source point) point :=
    intervalIntegral.integral_hasDerivAt_right (sourceContinuous.intervalIntegrable 0 point)
      sourceContinuous.stronglyMeasurable.stronglyMeasurableAtFilter sourceContinuous.continuousAt
  have primitiveContinuous : Continuous primitive :=
    continuous_iff_continuousAt.mpr fun point => (derivative point).continuousAt
  have constant := (continuous.sub primitiveContinuous).eq_const_of_integral_mul_deriv_eq_zero
    (fun test smooth compact => by
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
      rw [integral_sub functionProduct primitiveProduct, weak test smooth compact, primitiveIdentity]
      ring)
  have equality := constant first second
  have additive := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (sourceContinuous.intervalIntegrable 0 first) (sourceContinuous.intervalIntegrable first second)
  dsimp only [Pi.sub_apply, primitive] at equality
  linarith
