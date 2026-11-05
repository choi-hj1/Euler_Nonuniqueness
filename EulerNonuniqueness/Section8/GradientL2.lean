import EulerNonuniqueness.Section8.SharpEnergy

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology ContDiff InnerProductSpace

namespace EulerNonuniqueness

theorem hasCompactSupport_sub {first second : Vorticity}
    (firstCompact : HasCompactSupport first) (secondCompact : HasCompactSupport second) :
    HasCompactSupport (first - second) :=
  firstCompact.comp₂_left (m := fun first second : ℝ => first - second)
    secondCompact (sub_self (0 : ℝ))

theorem toReal_eLpNorm_two_sq_eq_integral {Value : Type*} [NormedAddCommGroup Value]
    [InnerProductSpace ℝ Value] {function : Plane → Value} (membership : MemLp function 2 volume) :
    (eLpNorm function 2 volume).toReal ^ 2 = ∫ position, ‖function position‖ ^ 2 := by
  rw [← Lp.norm_toLp function membership, ← real_inner_self_eq_norm_sq,
    L2.inner_def]
  apply integral_congr_ae
  filter_upwards [membership.coeFn_toLp] with position equality
  rw [equality, real_inner_self_eq_norm_sq]

theorem eLpNorm_gradient_biotSavart_sq {vorticity : Vorticity}
    (smooth : ContDiff ℝ ∞ vorticity) (compact : HasCompactSupport vorticity)
    (zeroMean : (∫ position, vorticity position) = 0) :
    (eLpNorm (fun position => fderiv ℝ (biotSavart vorticity) position 1) 2 volume).toReal ^ 2 +
      (eLpNorm (fun position => fderiv ℝ (biotSavart vorticity) position Complex.I) 2 volume).toReal ^ 2 =
        (eLpNorm vorticity 2 volume).toReal ^ 2 := by
  have firstMember := memLp_fderiv_biotSavart_apply smooth compact 1
  have secondMember := memLp_fderiv_biotSavart_apply smooth compact Complex.I
  have sourceMember : MemLp vorticity 2 volume :=
    smooth.continuous.memLp_of_hasCompactSupport compact
  rw [toReal_eLpNorm_two_sq_eq_integral firstMember,
    toReal_eLpNorm_two_sq_eq_integral secondMember,
    toReal_eLpNorm_two_sq_eq_integral sourceMember,
    ← integral_add (firstMember.integrable_norm_pow (by norm_num))
      (secondMember.integrable_norm_pow (by norm_num))]
  simpa only [Real.norm_eq_abs, sq_abs] using integral_gradient_biotSavart_sq smooth compact zeroMean

theorem eLpNorm_gradient_biotSavart_le {vorticity : Vorticity}
    (smooth : ContDiff ℝ ∞ vorticity) (compact : HasCompactSupport vorticity)
    (zeroMean : (∫ position, vorticity position) = 0) :
    (eLpNorm (fun position => fderiv ℝ (biotSavart vorticity) position 1) 2 volume).toReal ≤
        (eLpNorm vorticity 2 volume).toReal ∧
      (eLpNorm (fun position => fderiv ℝ (biotSavart vorticity) position Complex.I) 2 volume).toReal ≤
        (eLpNorm vorticity 2 volume).toReal := by
  have equality := eLpNorm_gradient_biotSavart_sq smooth compact zeroMean
  constructor <;> nlinarith [ENNReal.toReal_nonneg (a := eLpNorm vorticity 2 volume)]

theorem biotSavart_sub_of_continuous_compactSupport {first second : Vorticity}
    (firstContinuous : Continuous first) (firstCompact : HasCompactSupport first)
    (secondContinuous : Continuous second) (secondCompact : HasCompactSupport second) :
    biotSavart (first - second) = biotSavart first - biotSavart second := by
  funext position
  change (∫ source, (first source - second source) • biotSavartKernel (position - source)) = _
  simp_rw [sub_smul]
  exact integral_sub
    (firstCompact.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      firstContinuous locallyIntegrable_biotSavartKernel position)
    (secondCompact.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      secondContinuous locallyIntegrable_biotSavartKernel position)

def biotSavartGradientLp (vorticity : Vorticity) (smooth : ContDiff ℝ ∞ vorticity)
    (compact : HasCompactSupport vorticity) (direction : Plane) : Lp Plane 2 (volume : Measure Plane) :=
  (memLp_fderiv_biotSavart_apply smooth compact direction).toLp
    (fun position => fderiv ℝ (biotSavart vorticity) position direction)

theorem biotSavartGradientLp_sub {first second : Vorticity}
    (firstSmooth : ContDiff ℝ ∞ first) (firstCompact : HasCompactSupport first)
    (secondSmooth : ContDiff ℝ ∞ second) (secondCompact : HasCompactSupport second)
    (direction : Plane) :
    biotSavartGradientLp (first - second) (firstSmooth.sub secondSmooth)
        (hasCompactSupport_sub firstCompact secondCompact) direction =
      biotSavartGradientLp first firstSmooth firstCompact direction -
        biotSavartGradientLp second secondSmooth secondCompact direction := by
  have derivativeEquality :
      (fun position => fderiv ℝ (biotSavart (first - second)) position direction) =
      (fun position => fderiv ℝ (biotSavart first) position direction) -
        (fun position => fderiv ℝ (biotSavart second) position direction) := by
    funext position
    rw [biotSavart_sub_of_continuous_compactSupport firstSmooth.continuous firstCompact
      secondSmooth.continuous secondCompact]
    change (fderiv ℝ (fun point => biotSavart first point - biotSavart second point) position) direction = _
    rw [fderiv_sub
      ((contDiff_biotSavart_of_contDiff_compactSupport firstSmooth firstCompact).differentiable (by simp) position)
      ((contDiff_biotSavart_of_contDiff_compactSupport secondSmooth secondCompact).differentiable (by simp) position)]
    rfl
  apply Lp.ext
  filter_upwards [
    (memLp_fderiv_biotSavart_apply (firstSmooth.sub secondSmooth)
      (hasCompactSupport_sub firstCompact secondCompact) direction).coeFn_toLp,
    (memLp_fderiv_biotSavart_apply firstSmooth firstCompact direction).coeFn_toLp,
    (memLp_fderiv_biotSavart_apply secondSmooth secondCompact direction).coeFn_toLp,
    Lp.coeFn_sub (biotSavartGradientLp first firstSmooth firstCompact direction)
      (biotSavartGradientLp second secondSmooth secondCompact direction)]
    with position difference firstEquality secondEquality subtraction
  exact difference.trans ((congrFun derivativeEquality position).trans
    ((congrArg₂ (fun first second : Plane => first - second)
      firstEquality.symm secondEquality.symm).trans subtraction.symm))

theorem norm_biotSavartGradientLp_sub_le {first second : Vorticity}
    (firstSmooth : ContDiff ℝ ∞ first) (firstCompact : HasCompactSupport first)
    (secondSmooth : ContDiff ℝ ∞ second) (secondCompact : HasCompactSupport second)
    (firstMean : (∫ position, first position) = 0) (secondMean : (∫ position, second position) = 0)
    {direction : Plane} (basisDirection : direction = 1 ∨ direction = Complex.I) :
    ‖biotSavartGradientLp first firstSmooth firstCompact direction -
      biotSavartGradientLp second secondSmooth secondCompact direction‖ ≤
        (eLpNorm (first - second) 2 volume).toReal := by
  have differenceMean : (∫ position, (first - second) position) = 0 := by
    change (∫ position, first position - second position) = 0
    rw [integral_sub (firstSmooth.continuous.integrable_of_hasCompactSupport firstCompact)
      (secondSmooth.continuous.integrable_of_hasCompactSupport secondCompact), firstMean, secondMean, sub_self]
  rw [← biotSavartGradientLp_sub firstSmooth firstCompact secondSmooth secondCompact]
  rcases basisDirection with rfl | rfl
  · simpa only [biotSavartGradientLp, Lp.norm_toLp] using
      (eLpNorm_gradient_biotSavart_le (firstSmooth.sub secondSmooth)
        (hasCompactSupport_sub firstCompact secondCompact) differenceMean).1
  · simpa only [biotSavartGradientLp, Lp.norm_toLp] using
      (eLpNorm_gradient_biotSavart_le (firstSmooth.sub secondSmooth)
        (hasCompactSupport_sub firstCompact secondCompact) differenceMean).2

end EulerNonuniqueness
