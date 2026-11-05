import EulerNonuniqueness.General.LocalDerivativeLipschitz
import EulerNonuniqueness.Section6.NormalFormInverseMatching
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Set Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

private theorem paired_defect_bound
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    (chart field : Space → Space) {radius constant : ℝ}
    (radiusPositive : 0 < radius) (constantOne : 1 ≤ constant)
    (chartActual : ∀ point ∈ closedBall (0 : Space) radius, DifferentiableAt ℝ chart point)
    (fieldActual : ∀ point ∈ closedBall (0 : Space) radius, DifferentiableAt ℝ field point)
    (fieldZero : field 0 = 0) (chartJet : fderiv ℝ chart 0 = ContinuousLinearMap.id ℝ Space)
    (chartBound : ∀ point ∈ closedBall (0 : Space) radius, ‖fderiv ℝ chart point‖ ≤ constant)
    (fieldBound : ∀ point ∈ closedBall (0 : Space) radius, ‖fderiv ℝ field point‖ ≤ constant)
    (chartLip : ∀ first ∈ closedBall (0 : Space) radius, ∀ second ∈ closedBall (0 : Space) radius,
      ‖fderiv ℝ chart first - fderiv ℝ chart second‖ ≤ constant * ‖first - second‖)
    (fieldLip : ∀ first ∈ closedBall (0 : Space) radius, ∀ second ∈ closedBall (0 : Space) radius,
      ‖fderiv ℝ field first - fderiv ℝ field second‖ ≤ constant * ‖first - second‖)
    (first second : Space) (small : ‖first‖ + ‖second‖ ≤ radius) :
    ‖(fderiv ℝ chart first (field first) - fderiv ℝ field 0 (chart first)) -
        (fderiv ℝ chart second (field second) - fderiv ℝ field 0 (chart second))‖ ≤
      4 * constant ^ 2 * (‖first‖ + ‖second‖) * ‖first - second‖ := by
  have nonnegative : 0 ≤ constant := zero_le_one.trans constantOne
  have zeroInside : (0 : Space) ∈ closedBall (0 : Space) radius := mem_closedBall_self radiusPositive.le
  have firstInside : first ∈ closedBall (0 : Space) radius :=
    mem_closedBall_zero_iff.mpr ((le_add_of_nonneg_right (norm_nonneg second)).trans small)
  have secondInside : second ∈ closedBall (0 : Space) radius :=
    mem_closedBall_zero_iff.mpr ((le_add_of_nonneg_left (norm_nonneg first)).trans small)
  have residual (function : Space → Space)
      (actual : ∀ point ∈ closedBall (0 : Space) radius, DifferentiableAt ℝ function point)
      (lip : ∀ first ∈ closedBall (0 : Space) radius, ∀ second ∈ closedBall (0 : Space) radius,
        ‖fderiv ℝ function first - fderiv ℝ function second‖ ≤ constant * ‖first - second‖) :
      ‖function first - function second - fderiv ℝ function 0 (first - second)‖ ≤
        constant * (‖first‖ + ‖second‖) * ‖first - second‖ := by
    let size := ‖first‖ + ‖second‖
    have contained : closedBall (0 : Space) size ⊆ closedBall (0 : Space) radius :=
      closedBall_subset_closedBall small
    have estimate := (convex_closedBall (0 : Space) size).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun point => function point - fderiv ℝ function 0 point)
      (f' := fun point => fderiv ℝ function point - fderiv ℝ function 0)
      (fun point inside => ((actual point (contained inside)).hasFDerivAt.sub
        (fderiv ℝ function 0).hasFDerivAt).hasFDerivWithinAt)
      (fun point inside => (lip point (contained inside) 0 zeroInside).trans (by
        rw [sub_zero]
        exact mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp inside) nonnegative))
      (mem_closedBall_zero_iff.mpr (le_add_of_nonneg_left (norm_nonneg first)))
      (mem_closedBall_zero_iff.mpr (le_add_of_nonneg_right (norm_nonneg second)))
    convert estimate using 1
    congr 1
    simp only [map_sub]
    abel
  have fieldValue : ‖field first‖ ≤ constant * ‖first‖ := by
    have estimate := (convex_closedBall (0 : Space) radius).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun point inside => (fieldActual point inside).hasFDerivAt.hasFDerivWithinAt) fieldBound zeroInside firstInside
    simpa only [fieldZero, sub_zero] using estimate
  have chartDifference := chartLip first firstInside second secondInside
  have chartDeviation := chartLip second secondInside 0 zeroInside
  rw [chartJet, sub_zero] at chartDeviation
  have fieldResidual := residual field fieldActual fieldLip
  have chartResidual := residual chart chartActual chartLip
  rw [chartJet, ContinuousLinearMap.id_apply] at chartResidual
  let linear := fderiv ℝ field 0
  have linearBound : ‖linear‖ ≤ constant := fieldBound 0 zeroInside
  have identity :
      (fderiv ℝ chart first (field first) - linear (chart first)) -
        (fderiv ℝ chart second (field second) - linear (chart second)) =
      (fderiv ℝ chart first - fderiv ℝ chart second) (field first) +
        fderiv ℝ chart second (field first - field second - linear (first - second)) +
        (fderiv ℝ chart second - ContinuousLinearMap.id ℝ Space) (linear (first - second)) -
        linear (chart first - chart second - (first - second)) := by
    simp only [ContinuousLinearMap.sub_apply, map_sub, ContinuousLinearMap.id_apply]
    abel
  rw [identity]
  have firstTerm : ‖(fderiv ℝ chart first - fderiv ℝ chart second) (field first)‖ ≤
      constant ^ 2 * (‖first‖ + ‖second‖) * ‖first - second‖ := by
    apply ((fderiv ℝ chart first - fderiv ℝ chart second).le_opNorm _).trans
    have product := mul_le_mul chartDifference fieldValue (norm_nonneg _) (by positivity : 0 ≤ constant * ‖first - second‖)
    apply product.trans
    nlinarith only [mul_nonneg (sq_nonneg constant) (mul_nonneg (norm_nonneg second) (norm_nonneg (first - second)))]
  have secondTerm : ‖fderiv ℝ chart second (field first - field second - linear (first - second))‖ ≤
      constant ^ 2 * (‖first‖ + ‖second‖) * ‖first - second‖ := by
    apply ((fderiv ℝ chart second).le_opNorm _).trans
    convert mul_le_mul (chartBound second secondInside) fieldResidual (norm_nonneg _) nonnegative using 1
    ring
  have thirdTerm : ‖(fderiv ℝ chart second - ContinuousLinearMap.id ℝ Space) (linear (first - second))‖ ≤
      constant ^ 2 * (‖first‖ + ‖second‖) * ‖first - second‖ := by
    apply ((fderiv ℝ chart second - ContinuousLinearMap.id ℝ Space).le_opNorm _).trans
    have valueBound := (linear.le_opNorm (first - second)).trans
      (mul_le_mul_of_nonneg_right linearBound (norm_nonneg _))
    have product := mul_le_mul chartDeviation valueBound (norm_nonneg _) (by positivity : 0 ≤ constant * ‖second‖)
    apply product.trans
    nlinarith only [mul_nonneg (sq_nonneg constant) (mul_nonneg (norm_nonneg first) (norm_nonneg (first - second)))]
  have fourthTerm : ‖linear (chart first - chart second - (first - second))‖ ≤
      constant ^ 2 * (‖first‖ + ‖second‖) * ‖first - second‖ := by
    apply (linear.le_opNorm _).trans
    convert mul_le_mul linearBound chartResidual (norm_nonneg _) nonnegative using 1
    ring
  exact (norm_sub_le _ _).trans ((add_le_add ((norm_add₃_le).trans
    (add_le_add (add_le_add firstTerm secondTerm) thirdTerm)) fourthTerm).trans_eq (by ring))

private theorem exists_paired_defect_bound
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    {chart field : Space → Space} (chartSmooth : ContDiffAt ℝ 2 chart 0)
    (fieldSmooth : ContDiffAt ℝ 2 field 0) (fieldZero : field 0 = 0)
    (chartJet : fderiv ℝ chart 0 = ContinuousLinearMap.id ℝ Space) :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (1 : ℝ), ∀ first second : Space,
      ‖first‖ + ‖second‖ < radius →
      ‖(fderiv ℝ chart first (field first) - fderiv ℝ field 0 (chart first)) -
        (fderiv ℝ chart second (field second) - fderiv ℝ field 0 (chart second))‖ ≤
        constant * (‖first‖ + ‖second‖) * ‖first - second‖ := by
  obtain ⟨chartRadius, chartPositive, chartConstant, chartNonnegative, chartBound, chartLip⟩ :=
    General.exists_closedBall_fderiv_bound_of_contDiffAt_two chartSmooth
  obtain ⟨fieldRadius, fieldPositive, fieldConstant, fieldNonnegative, fieldBound, fieldLip⟩ :=
    General.exists_closedBall_fderiv_bound_of_contDiffAt_two fieldSmooth
  have nearby := (chartSmooth.eventually (by norm_num)).and (fieldSmooth.eventually (by norm_num))
  obtain ⟨regularRadius, regularPositive, regular⟩ := Metric.mem_nhds_iff.mp nearby
  let radius := min chartRadius (min fieldRadius (regularRadius / 2))
  let bound := 1 + chartConstant + fieldConstant
  have boundOne : 1 ≤ bound := by dsimp only [bound]; linarith only [chartNonnegative, fieldNonnegative]
  have chartLe : chartConstant ≤ bound := by dsimp only [bound]; linarith only [fieldNonnegative]
  have fieldLe : fieldConstant ≤ bound := by dsimp only [bound]; linarith only [chartNonnegative]
  have positive : 0 < radius := lt_min chartPositive (lt_min fieldPositive (half_pos regularPositive))
  have chartInside : closedBall (0 : Space) radius ⊆ closedBall (0 : Space) chartRadius :=
    closedBall_subset_closedBall (min_le_left _ _)
  have fieldInside : closedBall (0 : Space) radius ⊆ closedBall (0 : Space) fieldRadius :=
    closedBall_subset_closedBall ((min_le_right _ _).trans (min_le_left _ _))
  have regularInside (point : Space) (inside : point ∈ closedBall (0 : Space) radius) :=
    regular (show point ∈ ball (0 : Space) regularRadius from
      mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp inside).trans_lt
        (((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith only [regularPositive]))))
  refine ⟨radius, positive, 4 * bound ^ 2, by nlinarith only [boundOne, sq_nonneg (bound - 1)], ?_⟩
  intro first second small
  exact paired_defect_bound chart field positive boundOne
    (fun point inside => (regularInside point inside).1.differentiableAt (by norm_num))
    (fun point inside => (regularInside point inside).2.differentiableAt (by norm_num))
    fieldZero chartJet
    (fun point inside => (chartBound point (chartInside inside)).trans chartLe)
    (fun point inside => (fieldBound point (fieldInside inside)).trans fieldLe)
    (fun first firstMember second secondMember => (chartLip first (chartInside firstMember) second (chartInside secondMember)).trans
      (mul_le_mul_of_nonneg_right chartLe (norm_nonneg _)))
    (fun first firstMember second secondMember => (fieldLip first (fieldInside firstMember) second (fieldInside secondMember)).trans
      (mul_le_mul_of_nonneg_right fieldLe (norm_nonneg _)))
    first second small.le

theorem givenMap_localNormalFormError_paired_quadratic_bound
    {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (1 : ℝ), ∀ first second : ℝ × ℝ,
      |first.1| + |first.2| < radius → |second.1| + |second.2| < radius →
      let firstChart := localNormalFormChart graph coordinate first
      let secondChart := localNormalFormChart graph coordinate second
      let difference := |firstChart.1 - secondChart.1| + |firstChart.2 - secondChart.2|
      let referenceSize := |secondChart.1| + |secondChart.2|
      ‖localNormalFormError 1 graph coordinate first - localNormalFormError 1 graph coordinate second‖ ≤
        constant * difference * (difference + referenceSize) := by
  let chart := localNormalFormChart graph coordinate
  let field := shapeChartVelocity 1
  have regular := localNormalFormChart_regular graphSmooth coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨defectRadius, defectPositive, defectConstant, defectOne, defect⟩ :=
    exists_paired_defect_bound regular.1 (shapeChartVelocity_contDiffAt 1)
      (shapeChartVelocity_zero 1) regular.2.2.fderiv
  obtain ⟨inverseRadius, inversePositive, inverseConstant, inverseOne, inverse⟩ :=
    localNormalFormChart_exists_uniform_inverse_lipschitz graphSmooth coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  have nearby := (graphSmooth.eventually (by norm_num)).and (coordinateSmooth.eventually (by norm_num))
  obtain ⟨regularRadius, regularPositive, regularInside⟩ := Metric.mem_nhds_iff.mp nearby
  let radius := min (defectRadius / 2) (min inverseRadius regularRadius)
  let constant := 1 + 2 * defectConstant * inverseConstant ^ 2
  have constantOne : 1 ≤ constant := by
    have nonnegative : 0 ≤ 2 * defectConstant * inverseConstant ^ 2 := by positivity
    dsimp only [constant]
    linarith only [nonnegative]
  refine ⟨radius, lt_min (half_pos defectPositive) (lt_min inversePositive regularPositive), constant, constantOne, ?_⟩
  intro first second firstSmall secondSmall
  dsimp only
  have pointNorm (point : ℝ × ℝ) : ‖point‖ ≤ |point.1| + |point.2| := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
  have errorIdentity (point : ℝ × ℝ) (small : |point.1| + |point.2| < radius) :
      localNormalFormError 1 graph coordinate point =
        fderiv ℝ chart point (field point) - fderiv ℝ field 0 (chart point) := by
    have inside := regularInside (show point.1 ∈ ball (0 : ℝ) regularRadius by
      rw [mem_ball, dist_zero_right, Real.norm_eq_abs]
      exact (le_add_of_nonneg_right (abs_nonneg point.2)).trans_lt
        (small.trans_le ((min_le_right _ _).trans (min_le_right _ _))))
    have coordinateActual := inside.2.differentiableAt (by norm_num)
    have graphActual := inside.1.differentiableAt (by norm_num)
    have actual := (coordinateActual.hasDerivAt.comp_hasFDerivAt point (hasFDerivAt_fst (𝕜 := ℝ) (p := point))).prodMk
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := point)).sub
        (graphActual.hasDerivAt.comp_hasFDerivAt point (hasFDerivAt_fst (𝕜 := ℝ) (p := point))))
    have chartActual : HasFDerivAt chart
        ((deriv coordinate point.1 • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
          (ContinuousLinearMap.snd ℝ ℝ ℝ - deriv graph point.1 • ContinuousLinearMap.fst ℝ ℝ ℝ)) point := by
      simpa only [chart, localNormalFormChart, Function.comp_def] using actual
    rw [chartActual.fderiv]
    change _ = _ - fderiv ℝ (shapeChartVelocity 1) 0 (chart point)
    rw [shapeChartVelocity_fderiv]
    ext
    all_goals simp only [localNormalFormError, chart, field, localNormalFormChart, Prod.fst_sub, Prod.snd_sub,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.smul_apply, smul_eq_mul]
    all_goals ring
  rw [errorIdentity first firstSmall, errorIdentity second secondSmall]
  have defectSmall : ‖first‖ + ‖second‖ < defectRadius := by
    have firstBound := (pointNorm first).trans_lt (firstSmall.trans_le (min_le_left _ _))
    have secondBound := (pointNorm second).trans_lt (secondSmall.trans_le (min_le_left _ _))
    linarith only [firstBound, secondBound]
  have estimate := defect first second defectSmall
  have zeroSmall : |(0 : ℝ × ℝ).1| + |(0 : ℝ × ℝ).2| < inverseRadius := by simpa using inversePositive
  have firstInverse := inverse first 0 (firstSmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))) zeroSmall
  have secondInverse := inverse second 0 (secondSmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))) zeroSmall
  have differenceInverse := inverse first second
    (firstSmall.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    (secondSmall.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  rw [regular.2.1, sub_zero] at firstInverse secondInverse
  simp only [Prod.fst_zero, Prod.snd_zero, sub_zero] at firstInverse secondInverse
  let difference := |(chart first).1 - (chart second).1| + |(chart first).2 - (chart second).2|
  let referenceSize := |(chart second).1| + |(chart second).2|
  have chartNorm (point : ℝ × ℝ) : ‖point‖ ≤ |point.1| + |point.2| := pointNorm point
  have differenceNorm : ‖chart first - chart second‖ ≤ difference := by
    simpa only [Prod.fst_sub, Prod.snd_sub] using chartNorm (chart first - chart second)
  have chartFirst : ‖chart first‖ ≤ difference + referenceSize := by
    calc
      _ = ‖(chart first - chart second) + chart second‖ := by rw [sub_add_cancel]
      _ ≤ ‖chart first - chart second‖ + ‖chart second‖ := norm_add_le _ _
      _ ≤ _ := add_le_add differenceNorm (chartNorm _)
  have deltaNorm : ‖first - second‖ ≤ |first.1 - second.1| + |first.2 - second.2| := by
    simpa only [Prod.fst_sub, Prod.snd_sub] using pointNorm (first - second)
  have physicalDifference : ‖first - second‖ ≤ inverseConstant * difference :=
    deltaNorm.trans
      (differenceInverse.trans (mul_le_mul_of_nonneg_left differenceNorm (zero_le_one.trans inverseOne)))
  have physicalSum : ‖first‖ + ‖second‖ ≤ 2 * inverseConstant * (difference + referenceSize) := by
    have firstBound := (pointNorm first).trans (firstInverse.trans (mul_le_mul_of_nonneg_left chartFirst (zero_le_one.trans inverseOne)))
    have secondBound := (pointNorm second).trans (secondInverse.trans
      (mul_le_mul_of_nonneg_left (chartNorm _) (zero_le_one.trans inverseOne)))
    change ‖second‖ ≤ inverseConstant * referenceSize at secondBound
    have slack : 0 ≤ inverseConstant * difference := by dsimp only [difference]; positivity
    nlinarith only [firstBound, secondBound, slack]
  apply estimate.trans
  have product := mul_le_mul (mul_le_mul_of_nonneg_left physicalSum (zero_le_one.trans defectOne))
    physicalDifference (norm_nonneg _) (by positivity : 0 ≤ defectConstant * (2 * inverseConstant * (difference + referenceSize)))
  apply product.trans
  dsimp only [constant, difference, referenceSize, chart]
  nlinarith only [mul_nonneg (by positivity : 0 ≤ |(localNormalFormChart graph coordinate first).1 -
    (localNormalFormChart graph coordinate second).1| + |(localNormalFormChart graph coordinate first).2 -
    (localNormalFormChart graph coordinate second).2|) (by positivity : 0 ≤
      |(localNormalFormChart graph coordinate first).1 - (localNormalFormChart graph coordinate second).1| +
      |(localNormalFormChart graph coordinate first).2 - (localNormalFormChart graph coordinate second).2| +
      (|(localNormalFormChart graph coordinate second).1| + |(localNormalFormChart graph coordinate second).2|))]

end EulerNonuniqueness.Section6

