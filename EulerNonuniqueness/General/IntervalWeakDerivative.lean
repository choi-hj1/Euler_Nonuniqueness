import EulerNonuniqueness.General.LocalWeakDerivative
import EulerNonuniqueness.General.LocalizedIntegration

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

theorem ContinuousOn.sub_eq_intervalIntegral_of_weak_derivative_on_Icc
    {function source : ℝ → ℝ} {lower upper : ℝ}
    (continuous : ContinuousOn function (Icc lower upper))
    (sourceContinuous : ContinuousOn source (Icc lower upper))
    (ordered : lower < upper)
    (weak : ∀ test : ℝ → ℝ, ContDiff ℝ ∞ test → HasCompactSupport test →
      tsupport test ⊆ Ioo lower upper →
      (∫ point, function point * deriv test point) = -(∫ point, source point * test point))
    {first second : ℝ} (firstInside : first ∈ Icc lower upper)
    (secondInside : second ∈ Icc lower upper) :
    function second - function first = ∫ point in first..second, source point := by
  let extension := IccExtend ordered.le (fun point : Icc lower upper => function point)
  let sourceExtension := IccExtend ordered.le (fun point : Icc lower upper => source point)
  have extensionContinuous : Continuous extension :=
    continuous_IccExtend_iff.mpr (continuousOn_iff_continuous_restrict.mp continuous)
  have sourceExtensionContinuous : Continuous sourceExtension :=
    continuous_IccExtend_iff.mpr (continuousOn_iff_continuous_restrict.mp sourceContinuous)
  have extensionEquality (point : ℝ) (inside : point ∈ Icc lower upper) :
      extension point = function point := IccExtend_of_mem _ _ inside
  have sourceEquality (point : ℝ) (inside : point ∈ Icc lower upper) :
      sourceExtension point = source point := IccExtend_of_mem _ _ inside
  have extendedWeak (test : ℝ → ℝ) (smooth : ContDiff ℝ ∞ test)
      (compact : HasCompactSupport test) (contained : tsupport test ⊆ Ioo lower upper) :
      (∫ point, extension point * deriv test point) =
        -(∫ point, sourceExtension point * test point) := by
    have derivativeEquality : (fun point => extension point * deriv test point) =
        (fun point => function point * deriv test point) := by
      funext point
      by_cases inside : point ∈ Icc lower upper
      · rw [extensionEquality point inside]
      · have derivativeZero : deriv test point = 0 := by
          by_contra nonzero
          have inSupport : point ∈ Function.support (deriv test) := nonzero
          have bounds := contained (support_deriv_subset inSupport)
          exact inside ⟨bounds.1.le, bounds.2.le⟩
        simp only [derivativeZero, mul_zero]
    have sourceProductEquality : (fun point => sourceExtension point * test point) =
        (fun point => source point * test point) := by
      funext point
      by_cases inside : point ∈ Icc lower upper
      · rw [sourceEquality point inside]
      · have testZero : test point = 0 := by
          apply image_eq_zero_of_nmem_tsupport
          intro inSupport
          have bounds := contained inSupport
          exact inside ⟨bounds.1.le, bounds.2.le⟩
        simp only [testZero, mul_zero]
    rw [derivativeEquality, sourceProductEquality]
    exact weak test smooth compact contained
  have identity := extensionContinuous.sub_eq_intervalIntegral_of_weak_derivative_on_Icc
    sourceExtensionContinuous ordered extendedWeak firstInside secondInside
  rw [extensionEquality first firstInside, extensionEquality second secondInside] at identity
  exact identity.trans (intervalIntegral.integral_congr fun point inside =>
    sourceEquality point (uIcc_subset_Icc firstInside secondInside inside))

theorem ContinuousOn.norm_sub_le_of_weak_derivative_bound
    {function source : ℝ → ℝ} {lower upper bound : ℝ}
    (continuous : ContinuousOn function (Icc lower upper))
    (sourceContinuous : ContinuousOn source (Icc lower upper))
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

theorem ContinuousOn.sub_eq_intervalIntegral_of_weak_derivative_setIntegral
    {function source : ℝ → ℝ} {lower upper : ℝ}
    (continuous : ContinuousOn function (Icc lower upper))
    (sourceContinuous : ContinuousOn source (Icc lower upper))
    (ordered : lower < upper)
    (weak : ∀ test : ℝ → ℝ, ContDiff ℝ ∞ test → HasCompactSupport test →
      tsupport test ⊆ Ioo lower upper →
      (∫ point in Ioo lower upper,
        function point * deriv test point + source point * test point) = 0)
    {first second : ℝ} (firstInside : first ∈ Icc lower upper)
    (secondInside : second ∈ Icc lower upper) :
    function second - function first = ∫ point in first..second, source point := by
  refine continuous.sub_eq_intervalIntegral_of_weak_derivative_on_Icc sourceContinuous ordered
    ?_ firstInside secondInside
  intro test smooth compact contained
  have derivativeSupport : Function.support (deriv test) ⊆ Ioo lower upper :=
    support_deriv_subset.trans contained
  have testSupport : Function.support test ⊆ Ioo lower upper := (subset_tsupport test).trans contained
  have firstSupported : Function.support (fun point => function point * deriv test point) ⊆
      Icc lower upper := by
    intro point inside
    have derivativeNonzero : deriv test point ≠ 0 := right_ne_zero_of_mul inside
    have bounds := derivativeSupport derivativeNonzero
    exact ⟨bounds.1.le, bounds.2.le⟩
  have secondSupported : Function.support (fun point => source point * test point) ⊆
      Icc lower upper := by
    intro point inside
    have testNonzero : test point ≠ 0 := right_ne_zero_of_mul inside
    have bounds := testSupport testNonzero
    exact ⟨bounds.1.le, bounds.2.le⟩
  have firstIntegrable : Integrable (fun point => function point * deriv test point) :=
    (continuous.mul (smooth.continuous_deriv (by simp)).continuousOn).integrable_of_isCompact_of_support_subset
      isCompact_Icc firstSupported
  have secondIntegrable : Integrable (fun point => source point * test point) :=
    (sourceContinuous.mul smooth.continuous.continuousOn).integrable_of_isCompact_of_support_subset
      isCompact_Icc secondSupported
  have fullIntegral := weak test smooth compact contained
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun point outside => by
    have testZero : test point = 0 := Function.nmem_support.mp
      (fun inside => outside (testSupport inside))
    have derivativeZero : deriv test point = 0 := Function.nmem_support.mp
      (fun inside => outside (derivativeSupport inside))
    simp only [testZero, derivativeZero, mul_zero, add_zero]),
    integral_add firstIntegrable secondIntegrable] at fullIntegral
  linarith

theorem ContinuousOn.norm_sub_le_of_weak_derivative_setIntegral
    {function source : ℝ → ℝ} {lower upper bound : ℝ}
    (continuous : ContinuousOn function (Icc lower upper))
    (sourceContinuous : ContinuousOn source (Icc lower upper))
    (ordered : lower < upper)
    (weak : ∀ test : ℝ → ℝ, ContDiff ℝ ∞ test → HasCompactSupport test →
      tsupport test ⊆ Ioo lower upper →
      (∫ point in Ioo lower upper,
        function point * deriv test point + source point * test point) = 0)
    (bounded : ∀ point ∈ Icc lower upper, ‖source point‖ ≤ bound)
    {first second : ℝ} (firstInside : first ∈ Icc lower upper)
    (secondInside : second ∈ Icc lower upper) :
    ‖function second - function first‖ ≤ bound * |second - first| := by
  rw [continuous.sub_eq_intervalIntegral_of_weak_derivative_setIntegral
    sourceContinuous ordered weak firstInside secondInside]
  exact intervalIntegral.norm_integral_le_of_norm_le_const fun point inside =>
    bounded point (uIcc_subset_Icc firstInside secondInside (uIoc_subset_uIcc inside))
