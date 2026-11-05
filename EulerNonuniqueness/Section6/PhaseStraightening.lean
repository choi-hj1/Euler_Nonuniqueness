import EulerNonuniqueness.Section6.AdjustedPhase

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2

attribute [local fun_prop] ContDiffAt.sin ContDiffAt.cos

theorem shapeChartVelocity_analyticAt (frequency : ℝ) : AnalyticAt ℝ (shapeChartVelocity frequency) 0 := by
  have ratioPositive := rhombusRatio_pos
  have ratioNonzero : rhombusRatio ≠ 0 := ratioPositive.ne'
  have denominatorNonzero : 1 + rhombusRatio ^ 2 + 2 * rhombusRatio ≠ 0 := by positivity
  apply ContDiffAt.analyticAt
  unfold shapeChartVelocity radialVelocity shapeAngleVelocity shapeChartRatio shapeChartAngle
  fun_prop (disch := simp_all <;> positivity)

theorem adjustedPhaseError_analyticAt (frequency : ℝ) : AnalyticAt ℝ (adjustedPhaseError frequency) 0 := by
  have ratioPositive := rhombusRatio_pos
  have ratioNonzero : rhombusRatio ≠ 0 := ratioPositive.ne'
  have denominatorNonzero : 1 + rhombusRatio ^ 2 + 2 * rhombusRatio ≠ 0 := by positivity
  apply ContDiffAt.analyticAt
  unfold adjustedPhaseError rawAdjustedPhaseError rotationVelocity shapeAngleVelocity shapeChartRatio shapeChartAngle
  fun_prop (disch := simp_all <;> positivity)

def graphUnstableRate (frequency : ℝ) (graph : ℝ → ℝ) (unstable : ℝ) : ℝ :=
  (shapeChartVelocity frequency (unstable, graph unstable)).1

def graphAdjustedPhaseError (frequency : ℝ) (graph : ℝ → ℝ) (unstable : ℝ) : ℝ :=
  adjustedPhaseError frequency (unstable, graph unstable)

theorem graphPhaseFunctions_regular (frequency : ℝ) {graph : ℝ → ℝ}
    (graphAnalytic : AnalyticAt ℝ graph 0) (graphZero : graph 0 = 0) (graphDerivative : HasDerivAt graph 0 0) :
    AnalyticAt ℝ (graphUnstableRate frequency graph) 0 ∧
      AnalyticAt ℝ (graphAdjustedPhaseError frequency graph) 0 ∧
      graphUnstableRate frequency graph 0 = 0 ∧ graphAdjustedPhaseError frequency graph 0 = 0 ∧
      HasDerivAt (graphUnstableRate frequency graph) (2 * Real.sqrt 2 * frequency) 0 ∧
      HasDerivAt (graphAdjustedPhaseError frequency graph) 0 0 := by
  have pathOrder : ContDiffAt ℝ ω (fun unstable : ℝ => (unstable, graph unstable)) 0 :=
    contDiffAt_id.prodMk graphAnalytic.contDiffAt
  have pathZero : ((0 : ℝ), graph 0) = (0 : ℝ × ℝ) := by simp [graphZero]
  have fieldOrder : ContDiffAt ℝ ω (shapeChartVelocity frequency) ((0 : ℝ), graph 0) := by
    rw [pathZero]
    exact (shapeChartVelocity_analyticAt frequency).contDiffAt
  have phaseOrder : ContDiffAt ℝ ω (adjustedPhaseError frequency) ((0 : ℝ), graph 0) := by
    rw [pathZero]
    exact (adjustedPhaseError_analyticAt frequency).contDiffAt
  have fieldComposed : ContDiffAt ℝ ω (fun unstable => shapeChartVelocity frequency (unstable, graph unstable)) 0 :=
    ContDiffAt.comp (f := fun unstable => (unstable, graph unstable)) (g := shapeChartVelocity frequency)
      0 fieldOrder pathOrder
  have phaseComposed : ContDiffAt ℝ ω (graphAdjustedPhaseError frequency graph) 0 :=
    ContDiffAt.comp (f := fun unstable => (unstable, graph unstable)) (g := adjustedPhaseError frequency)
      0 phaseOrder pathOrder
  have pathDerivative : HasDerivAt (fun unstable : ℝ => (unstable, graph unstable)) ((1 : ℝ), (0 : ℝ)) 0 :=
    (hasDerivAt_id (0 : ℝ)).prodMk graphDerivative
  have fieldBase : HasFDerivAt (shapeChartVelocity frequency)
      (fderiv ℝ (shapeChartVelocity frequency) 0) ((0 : ℝ), graph 0) := by
    rw [pathZero]
    exact ((shapeChartVelocity_contDiffAt frequency).differentiableAt (by norm_num)).hasFDerivAt
  have fieldDerivative : HasDerivAt (fun unstable => shapeChartVelocity frequency (unstable, graph unstable))
      (2 * Real.sqrt 2 * frequency, (0 : ℝ)) 0 := by
    convert HasFDerivAt.comp_hasDerivAt (l := shapeChartVelocity frequency)
      (l' := fderiv ℝ (shapeChartVelocity frequency) 0) (0 : ℝ) fieldBase pathDerivative using 1
    rw [shapeChartVelocity_fderiv]
    simp
  have unstableDerivative : HasDerivAt (graphUnstableRate frequency graph) (2 * Real.sqrt 2 * frequency) 0 :=
    HasFDerivAt.comp_hasDerivAt (l := Prod.fst) (l' := ContinuousLinearMap.fst ℝ ℝ ℝ)
      (0 : ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt fieldDerivative
  have phaseBase : HasFDerivAt (adjustedPhaseError frequency) (0 : (ℝ × ℝ) →L[ℝ] ℝ) ((0 : ℝ), graph 0) := by
    rw [pathZero]
    exact (adjustedPhaseError_regular frequency).2.2
  have phaseDerivative : HasDerivAt (graphAdjustedPhaseError frequency graph) 0 0 := by
    simpa only [ContinuousLinearMap.zero_apply] using HasFDerivAt.comp_hasDerivAt
      (l := adjustedPhaseError frequency) (l' := (0 : (ℝ × ℝ) →L[ℝ] ℝ)) (0 : ℝ) phaseBase pathDerivative
  refine ⟨fieldComposed.fst.analyticAt, phaseComposed.analyticAt, ?_, ?_, unstableDerivative, phaseDerivative⟩
  · simp [graphUnstableRate, graphZero, shapeChartVelocity_zero]
  · simpa only [graphAdjustedPhaseError, graphZero, Prod.mk_zero_zero] using (adjustedPhaseError_regular frequency).2.1

def phaseCorrectionIntegrand (frequency : ℝ) (graph : ℝ → ℝ) (unstable : ℝ) : ℝ :=
  dslope (graphAdjustedPhaseError frequency graph) 0 unstable / dslope (graphUnstableRate frequency graph) 0 unstable

theorem phaseCorrectionIntegrand_regular (frequency : ℝ) (frequencyNonzero : frequency ≠ 0)
    {graph : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (graphZero : graph 0 = 0) (graphDerivative : HasDerivAt graph 0 0) :
    AnalyticAt ℝ (phaseCorrectionIntegrand frequency graph) 0 ∧
      phaseCorrectionIntegrand frequency graph 0 = 0 ∧
      ∀ᶠ unstable in nhds (0 : ℝ),
        phaseCorrectionIntegrand frequency graph unstable * graphUnstableRate frequency graph unstable =
          graphAdjustedPhaseError frequency graph unstable := by
  have regular := graphPhaseFunctions_regular frequency graphAnalytic graphZero graphDerivative
  obtain ⟨rateSeries, rateProperty⟩ := regular.1
  obtain ⟨phaseSeries, phaseProperty⟩ := regular.2.1
  have rateSlopeAnalytic : AnalyticAt ℝ (dslope (graphUnstableRate frequency graph) 0) 0 :=
    ⟨rateSeries.fslope, rateProperty.has_fpower_series_dslope_fslope⟩
  have phaseSlopeAnalytic : AnalyticAt ℝ (dslope (graphAdjustedPhaseError frequency graph) 0) 0 :=
    ⟨phaseSeries.fslope, phaseProperty.has_fpower_series_dslope_fslope⟩
  have rateSlopeNonzero : dslope (graphUnstableRate frequency graph) 0 0 ≠ 0 := by
    rw [dslope_same, regular.2.2.2.2.1.deriv]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne') frequencyNonzero
  refine ⟨phaseSlopeAnalytic.div rateSlopeAnalytic rateSlopeNonzero, ?_, ?_⟩
  · simp only [phaseCorrectionIntegrand, dslope_same, regular.2.2.2.2.2.deriv, zero_div]
  · filter_upwards [rateSlopeAnalytic.continuousAt.eventually_ne rateSlopeNonzero] with unstable denominatorNonzero
    have phaseIdentity := sub_smul_dslope (graphAdjustedPhaseError frequency graph) 0 unstable
    have rateIdentity := sub_smul_dslope (graphUnstableRate frequency graph) 0 unstable
    rw [smul_eq_mul, sub_zero, regular.2.2.1, sub_zero] at rateIdentity
    rw [smul_eq_mul, sub_zero, regular.2.2.2.1, sub_zero] at phaseIdentity
    unfold phaseCorrectionIntegrand
    rw [← rateIdentity]
    field_simp
    linear_combination dslope (graphUnstableRate frequency graph) 0 unstable * phaseIdentity

def phaseCorrection (frequency : ℝ) (graph : ℝ → ℝ) (unstable : ℝ) : ℝ :=
  ∫ current in (0 : ℝ)..unstable, phaseCorrectionIntegrand frequency graph current

theorem phaseCorrection_regular (frequency : ℝ) (frequencyNonzero : frequency ≠ 0)
    {graph : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (graphZero : graph 0 = 0) (graphDerivative : HasDerivAt graph 0 0) :
    ContDiffAt ℝ 2 (phaseCorrection frequency graph) 0 ∧ phaseCorrection frequency graph 0 = 0 ∧
      HasDerivAt (phaseCorrection frequency graph) 0 0 ∧
      ∀ᶠ unstable in nhds (0 : ℝ),
        deriv (phaseCorrection frequency graph) unstable * graphUnstableRate frequency graph unstable =
          graphAdjustedPhaseError frequency graph unstable := by
  have regular := phaseCorrectionIntegrand_regular frequency frequencyNonzero graphAnalytic graphZero graphDerivative
  have primitive := local_primitive_regular (regular.1.contDiffAt (n := 1))
  have initialDerivative : HasDerivAt (phaseCorrection frequency graph) 0 0 := by
    simpa only [regular.2.1] using primitive.2.self_of_nhds
  refine ⟨primitive.1, by simp [phaseCorrection], initialDerivative, ?_⟩
  filter_upwards [primitive.2, regular.2.2] with unstable primitiveDerivative identity
  change deriv (fun endpoint => ∫ current in (0 : ℝ)..endpoint,
    phaseCorrectionIntegrand frequency graph current) unstable * graphUnstableRate frequency graph unstable = _
  rw [primitiveDerivative.deriv]
  exact identity

def correctedPhaseError (frequency : ℝ) (correction : ℝ → ℝ) (point : ℝ × ℝ) : ℝ :=
  adjustedPhaseError frequency point - deriv correction point.1 * (shapeChartVelocity frequency point).1

def correctedPhaseCoefficient (frequency : ℝ) (correction : ℝ → ℝ) (point : ℝ × ℝ) : ℝ :=
  fderiv ℝ (adjustedPhaseError frequency) point (0, 1) -
    deriv correction point.1 * (fderiv ℝ (shapeChartVelocity frequency) point (0, 1)).1

theorem correctedPhaseCoefficient_regular (frequency : ℝ) {correction : ℝ → ℝ}
    (correctionSmooth : ContDiffAt ℝ 2 correction 0) (correctionDerivative : HasDerivAt correction 0 0) :
    ContDiffAt ℝ 1 (correctedPhaseCoefficient frequency correction) 0 ∧
      correctedPhaseCoefficient frequency correction 0 = 0 := by
  have phasePartial : ContDiffAt ℝ 1
      (fun point : ℝ × ℝ => fderiv ℝ (adjustedPhaseError frequency) point (0, 1)) 0 :=
    ((adjustedPhaseError_regular frequency).1.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have fieldPartial : ContDiffAt ℝ 1
      (fun point : ℝ × ℝ => fderiv ℝ (shapeChartVelocity frequency) point (0, 1)) 0 :=
    ((shapeChartVelocity_contDiffAt frequency).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have correctionPartial : ContDiffAt ℝ 1 (fun point : ℝ × ℝ => deriv correction point.1) 0 :=
    ContDiffAt.comp (f := Prod.fst) (g := deriv correction) 0
      (scalar_deriv_contDiffAt_one correctionSmooth) contDiffAt_fst
  refine ⟨phasePartial.sub (correctionPartial.mul fieldPartial.fst), ?_⟩
  simp [correctedPhaseCoefficient, (adjustedPhaseError_regular frequency).2.2.fderiv,
    ContinuousLinearMap.zero_apply, correctionDerivative.deriv, mul_zero, zero_mul, sub_zero]

theorem correctedPhaseError_vertical_derivative (frequency : ℝ) (correction : ℝ → ℝ) :
    ∀ᶠ point in nhds (0 : ℝ × ℝ), HasDerivAt
      (fun stable => correctedPhaseError frequency correction (point.1, stable))
      (correctedPhaseCoefficient frequency correction point) point.2 := by
  have phaseSmooth := (adjustedPhaseError_regular frequency).1.eventually (by norm_num)
  have fieldSmooth := (shapeChartVelocity_contDiffAt frequency).eventually (by norm_num)
  filter_upwards [phaseSmooth, fieldSmooth] with point phaseSmooth fieldSmooth
  have path : HasDerivAt (fun stable : ℝ => (point.1, stable)) ((0 : ℝ), (1 : ℝ)) point.2 :=
    (hasDerivAt_const point.2 point.1).prodMk (hasDerivAt_id point.2)
  have phaseDerivative : HasDerivAt (fun stable => adjustedPhaseError frequency (point.1, stable))
      (fderiv ℝ (adjustedPhaseError frequency) point (0, 1)) point.2 :=
    HasFDerivAt.comp_hasDerivAt (l := adjustedPhaseError frequency)
      (l' := fderiv ℝ (adjustedPhaseError frequency) point) point.2
        (phaseSmooth.differentiableAt (by norm_num)).hasFDerivAt path
  have fieldDerivative : HasDerivAt (fun stable : ℝ => shapeChartVelocity frequency (point.1, stable))
      (fderiv ℝ (shapeChartVelocity frequency) point (0, 1)) point.2 :=
    HasFDerivAt.comp_hasDerivAt (l := shapeChartVelocity frequency)
      (l' := fderiv ℝ (shapeChartVelocity frequency) point) point.2
        (fieldSmooth.differentiableAt (by norm_num)).hasFDerivAt path
  have firstComponent : HasDerivAt (fun stable : ℝ => (shapeChartVelocity frequency (point.1, stable)).1)
      (fderiv ℝ (shapeChartVelocity frequency) point (0, 1)).1 point.2 :=
    HasFDerivAt.comp_hasDerivAt (l := Prod.fst) (l' := ContinuousLinearMap.fst ℝ ℝ ℝ)
      point.2 (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt fieldDerivative
  exact phaseDerivative.sub (firstComponent.const_mul (deriv correction point.1))

theorem phaseCorrection_stable_factor (frequency : ℝ) (frequencyNonzero : frequency ≠ 0)
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (graphZero : graph 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateZero : coordinate 0 = 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ unstable stable : ℝ,
      |unstable| + |stable| < radius →
        |correctedPhaseError frequency (phaseCorrection frequency graph) (unstable, stable)| ≤
          bound * |stable - graph unstable| * (|coordinate unstable| + |stable - graph unstable|) := by
  have regular := phaseCorrection_regular frequency frequencyNonzero graphAnalytic graphZero graphDerivative
  have coefficientRegular := correctedPhaseCoefficient_regular frequency regular.1 regular.2.2.1
  have vanishing : ∀ᶠ unstable in nhds (0 : ℝ),
      correctedPhaseError frequency (phaseCorrection frequency graph) (unstable, graph unstable) = 0 := by
    filter_upwards [regular.2.2.2] with unstable identity
    exact sub_eq_zero.mpr identity.symm
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    fiber_vanishing_quadratic_bound graphAnalytic.continuousAt graphZero coefficientRegular.1 coefficientRegular.2
      (correctedPhaseError_vertical_derivative frequency (phaseCorrection frequency graph)) vanishing
  obtain ⟨graphBound, graphBoundPositive, graphEstimate⟩ := graphDerivative.isBigO_sub.exists_pos
  obtain ⟨inverseBound, inverseBoundPositive, inverseEstimate⟩ :=
    (coordinateDerivative.isBigO_sub_rev (by norm_num)).exists_pos
  have comparison : ∀ᶠ unstable in nhds (0 : ℝ),
      |graph unstable| ≤ graphBound * |unstable| ∧ |unstable| ≤ inverseBound * |coordinate unstable| := by
    filter_upwards [graphEstimate.bound, inverseEstimate.bound] with unstable graphEstimate inverseEstimate
    simpa only [graphZero, coordinateZero, sub_zero, Real.norm_eq_abs] using And.intro graphEstimate inverseEstimate
  obtain ⟨comparisonRadius, comparisonRadiusPositive, comparisonInside⟩ := Metric.mem_nhds_iff.mp comparison
  let sizeConstant := (1 + 2 * graphBound) * inverseBound + 1
  refine ⟨bound * sizeConstant, by dsimp [sizeConstant]; positivity,
    min radius comparisonRadius, by positivity, ?_⟩
  intro unstable stable sizeBound
  have comparison := comparisonInside (show unstable ∈ Metric.ball (0 : ℝ) comparisonRadius by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    exact (lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg stable)) sizeBound).trans_le (min_le_right _ _))
  have originalBound := estimate unstable stable (sizeBound.trans_le (min_le_left _ _))
  have stableTriangle : |stable| ≤ |stable - graph unstable| + |graph unstable| := by
    simpa only [sub_add_cancel] using abs_add (stable - graph unstable) (graph unstable)
  have graphSize : |unstable| + 2 * |graph unstable| ≤
      ((1 + 2 * graphBound) * inverseBound) * |coordinate unstable| := by
    have amplified := mul_le_mul_of_nonneg_left comparison.2 (show 0 ≤ 1 + 2 * graphBound by positivity)
    nlinarith [comparison.1]
  have sizeComparison : |unstable| + |stable| + |graph unstable| ≤
      sizeConstant * (|coordinate unstable| + |stable - graph unstable|) := by
    have positiveProduct : 0 ≤ ((1 + 2 * graphBound) * inverseBound) * |stable - graph unstable| := by positivity
    dsimp [sizeConstant]
    nlinarith [abs_nonneg (coordinate unstable)]
  exact originalBound.trans (by
    convert mul_le_mul_of_nonneg_left sizeComparison
      (mul_nonneg boundNonnegative (abs_nonneg (stable - graph unstable))) using 1 <;> ring)

theorem quadrupole_shape_phase_normal_form_exists (frequency : ℝ) (frequencyNonzero : frequency ≠ 0) :
    ∃ graph coordinate correction : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ContDiffAt ℝ 2 correction 0 ∧ correction 0 = 0 ∧ HasDerivAt correction 0 0 ∧
      ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ unstable stable : ℝ,
        |unstable| + |stable| < radius →
        |(localNormalFormError frequency graph coordinate (unstable, stable)).1| +
          |(localNormalFormError frequency graph coordinate (unstable, stable)).2| +
          |correctedPhaseError frequency correction (unstable, stable)| ≤
          bound * |stable - graph unstable| * (|coordinate unstable| + |stable - graph unstable|) := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, shapeBound, shapeBoundNonnegative, shapeRadius, shapeRadiusPositive, shapeEstimate⟩ :=
      localNormalForm_quadratic_stable_remainder_exists frequency frequencyNonzero
  have phaseRegular := phaseCorrection_regular frequency frequencyNonzero graphAnalytic graphZero graphDerivative
  obtain ⟨phaseBound, phaseBoundNonnegative, phaseRadius, phaseRadiusPositive, phaseEstimate⟩ :=
    phaseCorrection_stable_factor frequency frequencyNonzero graphAnalytic graphZero graphDerivative
      coordinateZero coordinateDerivative
  refine ⟨graph, coordinate, phaseCorrection frequency graph, graphAnalytic, graphZero, graphDerivative,
    coordinateSmooth, coordinateZero, coordinateDerivative, phaseRegular.1, phaseRegular.2.1, phaseRegular.2.2.1,
      shapeBound + phaseBound, by positivity, min shapeRadius phaseRadius, by positivity, ?_⟩
  intro unstable stable sizeBound
  have shape := shapeEstimate unstable stable (sizeBound.trans_le (min_le_left _ _))
  have phase := phaseEstimate unstable stable (sizeBound.trans_le (min_le_right _ _))
  nlinarith

theorem correctedPhase_forced_equation {correction phase : ℝ → ℝ} {trajectory : ℝ → ℝ × ℝ}
    {frequency time phaseForcing : ℝ} {forcing : ℝ × ℝ}
    (equation : HasDerivAt trajectory (shapeChartVelocity frequency (trajectory time) + forcing) time)
    (phaseEquation : HasDerivAt phase
      (-frequency + adjustedPhaseError frequency (trajectory time) + phaseForcing) time)
    (correctionDifferentiable : DifferentiableAt ℝ correction (trajectory time).1) :
    HasDerivAt (fun currentTime => phase currentTime - correction (trajectory currentTime).1)
      (-frequency + correctedPhaseError frequency correction (trajectory time) + phaseForcing -
        deriv correction (trajectory time).1 * forcing.1) time := by
  have firstComponent : HasDerivAt (fun currentTime => (trajectory currentTime).1)
      ((shapeChartVelocity frequency (trajectory time)).1 + forcing.1) time :=
    HasFDerivAt.comp_hasDerivAt (l := Prod.fst) (l' := ContinuousLinearMap.fst ℝ ℝ ℝ)
      time (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt equation
  convert phaseEquation.sub (correctionDifferentiable.hasDerivAt.comp time firstComponent) using 1
  dsimp [correctedPhaseError]
  ring

end EulerNonuniqueness.Section6
