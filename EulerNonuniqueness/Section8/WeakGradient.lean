import EulerNonuniqueness.Section8.MollifiedGradient
import EulerNonuniqueness.Section8.MollifiedVelocity

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff InnerProductSpace

namespace EulerNonuniqueness

theorem tendsto_integral_smul_of_L2_tendsto
    {sequence : ℕ → Lp Plane 2 (volume : Measure Plane)} {limit : Lp Plane 2 (volume : Measure Plane)}
    (converges : Tendsto sequence atTop (𝓝 limit)) {test : Plane → ℝ} (testMember : MemLp test 2 volume) :
    Tendsto (fun index => ∫ position, test position • sequence index position) atTop
      (𝓝 (∫ position, test position • limit position)) := by
  have complexMember := Complex.ofRealCLM.comp_memLp' testMember
  let testLp := complexMember.toLp (Complex.ofRealCLM ∘ test)
  have pairing (field : Lp Plane 2 (volume : Measure Plane)) :
      innerSL ℂ testLp field = ∫ position, test position • field position := by
    rw [innerSL_apply, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [complexMember.coeFn_toLp] with position equality
    simp only [testLp] at *
    rw [equality]
    simp only [Function.comp_apply, Complex.ofRealCLM_apply, RCLike.inner_apply',
      Complex.conj_ofReal, Complex.real_smul]
  have paired := ((innerSL ℂ testLp).continuous.tendsto limit).comp converges
  change Tendsto (fun index => innerSL ℂ testLp (sequence index)) atTop (𝓝 (innerSL ℂ testLp limit)) at paired
  simpa only [pairing] using paired

theorem integral_test_fderiv_biotSavart {vorticity : Vorticity}
    (smooth : ContDiff ℝ ∞ vorticity) (compact : HasCompactSupport vorticity)
    {test : Plane → ℝ} (testSmooth : ContDiff ℝ ∞ test) (testCompact : HasCompactSupport test)
    (direction : Plane) :
    (∫ position, test position • fderiv ℝ (biotSavart vorticity) position direction) =
      -(∫ position, fderiv ℝ test position direction • biotSavart vorticity position) := by
  have velocitySmooth := contDiff_biotSavart_of_contDiff_compactSupport smooth compact
  have velocityDerivative : Continuous (fun position => fderiv ℝ (biotSavart vorticity) position direction) :=
    (velocitySmooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have testDerivative : Continuous (fun position => fderiv ℝ test position direction) :=
    (testSmooth.continuous_fderiv (by simp)).clm_apply continuous_const
  exact integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume)
    ((testDerivative.smul velocitySmooth.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.smul_right (testCompact.fderiv_apply ℝ direction)))
    ((testSmooth.continuous.smul velocityDerivative).integrable_of_hasCompactSupport
      testCompact.smul_right)
    ((testSmooth.continuous.smul velocitySmooth.continuous).integrable_of_hasCompactSupport
      testCompact.smul_right)
    (testSmooth.differentiable (by simp)) (velocitySmooth.differentiable (by simp))

theorem exists_weakL2_derivative_biotSavart {vorticity : Vorticity} {radius : ℝ}
    (radiusNonnegative : 0 ≤ radius)
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp vorticity (ENNReal.ofReal exponent) volume)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (zeroMean : (∫ position, vorticity position) = 0)
    {direction : Plane} (basisDirection : direction = 1 ∨ direction = Complex.I) :
    ∃ gradient : Lp Plane 2 (volume : Measure Plane),
      ‖gradient‖ ≤ (eLpNorm vorticity 2 volume).toReal ∧ ∀ test : Plane → ℝ,
      ContDiff ℝ ∞ test → HasCompactSupport test →
      Integrable (fun position => test position • gradient position) ∧
      Integrable (fun position => fderiv ℝ test position direction • biotSavart vorticity position) ∧
      (∫ position, test position • gradient position) =
        -(∫ position, fderiv ℝ test position direction • biotSavart vorticity position) := by
  have integrable : Integrable vorticity :=
    memLp_one_iff_integrable.mp (by simpa using membership 1 le_rfl)
  obtain ⟨gradient, gradientConverges⟩ :=
    exists_mollifiedGradient_limit integrable membership supportBound zeroMean basisDirection
  have sourceMember : MemLp vorticity 2 volume := by simpa using membership 2 (by norm_num)
  have normBound (index : ℕ) :
      ‖biotSavartGradientLp (mollification vorticity index) (contDiff_mollification integrable index)
        (hasCompactSupport_mollification supportBound index) direction‖ ≤ (eLpNorm vorticity 2 volume).toReal := by
    have meanZero : (∫ position, mollification vorticity index position) = 0 := by
      rw [integral_mollification integrable index, zeroMean]
    have gradientBound := eLpNorm_gradient_biotSavart_le (contDiff_mollification integrable index)
      (hasCompactSupport_mollification supportBound index) meanZero
    have mollifiedBound : (eLpNorm (mollification vorticity index) 2 volume).toReal ≤
        (eLpNorm vorticity 2 volume).toReal :=
      ENNReal.toReal_mono sourceMember.eLpNorm_ne_top
        (eLpNorm_mollification_nat_le integrable supportBound (by norm_num : 0 < 2) sourceMember index)
    rcases basisDirection with rfl | rfl
    · calc
        _ ≤ (eLpNorm (mollification vorticity index) 2 volume).toReal := by
          simpa only [biotSavartGradientLp, Lp.norm_toLp] using gradientBound.1
        _ ≤ _ := mollifiedBound
    · calc
        _ ≤ (eLpNorm (mollification vorticity index) 2 volume).toReal := by
          simpa only [biotSavartGradientLp, Lp.norm_toLp] using gradientBound.2
        _ ≤ _ := mollifiedBound
  have gradientNormBound : ‖gradient‖ ≤ (eLpNorm vorticity 2 volume).toReal :=
    le_of_tendsto' (continuous_norm.tendsto gradient |>.comp gradientConverges) normBound
  refine ⟨gradient, gradientNormBound, fun test testSmooth testCompact => ?_⟩
  have testMember : MemLp test 2 volume := testSmooth.continuous.memLp_of_hasCompactSupport testCompact
  have testDerivative : Continuous (fun position => fderiv ℝ test position direction) :=
    (testSmooth.continuous_fderiv (by simp)).clm_apply continuous_const
  refine ⟨memLp_one_iff_integrable.mp ((Lp.memLp gradient).smul testMember),
    (locallyIntegrable_biotSavart_of_integrable_support integrable supportBound).integrable_smul_left_of_hasCompactSupport
      testDerivative (testCompact.fderiv_apply ℝ direction), ?_⟩
  have pairingConverges := tendsto_integral_smul_of_L2_tendsto gradientConverges testMember
  have pairingEquality (index : ℕ) :
      (∫ position, test position • biotSavartGradientLp (mollification vorticity index)
        (contDiff_mollification integrable index) (hasCompactSupport_mollification supportBound index) direction position) =
        ∫ position, test position • fderiv ℝ (biotSavart (mollification vorticity index)) position direction := by
    apply integral_congr_ae
    filter_upwards [(memLp_fderiv_biotSavart_apply (contDiff_mollification integrable index)
      (hasCompactSupport_mollification supportBound index) direction).coeFn_toLp] with position equality
    exact congrArg (fun value : Plane => test position • value) equality
  simp_rw [pairingEquality] at pairingConverges
  have velocityConverges := tendsto_integral_smul_biotSavart_mollification radiusNonnegative membership supportBound
    testDerivative (testCompact.fderiv_apply ℝ direction)
  have identity :
      (fun index => ∫ position, test position • fderiv ℝ (biotSavart (mollification vorticity index)) position direction) =
      (fun index => -(∫ position, fderiv ℝ test position direction •
        biotSavart (mollification vorticity index) position)) :=
    funext fun index => integral_test_fderiv_biotSavart (contDiff_mollification integrable index)
      (hasCompactSupport_mollification supportBound index) testSmooth testCompact direction
  rw [identity] at pairingConverges
  exact tendsto_nhds_unique pairingConverges velocityConverges.neg

end EulerNonuniqueness
