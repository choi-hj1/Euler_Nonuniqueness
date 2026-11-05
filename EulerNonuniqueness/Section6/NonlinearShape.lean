import EulerNonuniqueness.Section2.PointVortices
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

attribute [local fun_prop] ContDiffAt.sin ContDiffAt.cos

theorem contDiffAt_quadratic_remainder {domain codomain : Type*}
    [NormedAddCommGroup domain] [NormedSpace ℝ domain]
    [NormedAddCommGroup codomain] [NormedSpace ℝ codomain]
    {function : domain → codomain}
    (smooth : ContDiffAt ℝ 2 function 0) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ point : domain, ‖point‖ < radius →
      ‖function point - function 0 - fderiv ℝ function 0 point‖ ≤ bound * ‖point‖ ^ 2 := by
  obtain ⟨bound, neighborhood, neighborhoodMem, lipschitz⟩ :=
    (smooth.fderiv_right (m := 1) (by norm_num)).exists_lipschitzOnWith
  have smoothEventually := smooth.eventually (by norm_num)
  obtain ⟨radius, radiusPositive, ballInside⟩ := Metric.mem_nhds_iff.mp
    (inter_mem neighborhoodMem smoothEventually)
  refine ⟨bound, bound.coe_nonneg, radius, radiusPositive, ?_⟩
  intro point pointBound
  have inside : Metric.closedBall (0 : domain) ‖point‖ ⊆ neighborhood ∩
      {currentPoint | ContDiffAt ℝ 2 function currentPoint} := by
    intro currentPoint currentBound
    apply ballInside
    simp only [Metric.mem_ball, dist_zero_right]
    have currentNormBound : ‖currentPoint‖ ≤ ‖point‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using currentBound
    exact currentNormBound.trans_lt pointBound
  have zeroInside : (0 : domain) ∈ Metric.closedBall (0 : domain) ‖point‖ := by simp
  have derivative : ∀ currentPoint ∈ Metric.closedBall (0 : domain) ‖point‖,
      HasFDerivWithinAt (fun currentPoint => function currentPoint - function 0 -
        fderiv ℝ function 0 currentPoint)
        (fderiv ℝ function currentPoint - fderiv ℝ function 0)
        (Metric.closedBall (0 : domain) ‖point‖) currentPoint := by
    intro currentPoint currentBound
    have currentSmooth : ContDiffAt ℝ 2 function currentPoint := (inside currentBound).2
    simpa only [sub_zero] using ((currentSmooth.differentiableAt (by norm_num)).hasFDerivAt.sub
      (hasFDerivAt_const (function 0) currentPoint) |>.sub
        (fderiv ℝ function 0).hasFDerivAt).hasFDerivWithinAt
  have derivativeBound : ∀ currentPoint ∈ Metric.closedBall (0 : domain) ‖point‖,
      ‖fderiv ℝ function currentPoint - fderiv ℝ function 0‖ ≤ (bound : ℝ) * ‖point‖ := by
    intro currentPoint currentBound
    calc
      _ ≤ (bound : ℝ) * ‖currentPoint - 0‖ :=
        (lipschitzOnWith_iff_norm_sub_le.mp lipschitz) (inside currentBound).1
          (inside zeroInside).1
      _ ≤ _ := by
        simp only [sub_zero]
        exact mul_le_mul_of_nonneg_left
          (by simpa only [Metric.mem_closedBall, dist_zero_right] using currentBound) bound.coe_nonneg
  have estimate := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le derivative derivativeBound
    (convex_closedBall (0 : domain) ‖point‖) zeroInside
      (show point ∈ Metric.closedBall (0 : domain) ‖point‖ by simp)
  simpa only [map_zero, sub_self, sub_zero, mul_pow, pow_two, mul_assoc] using estimate

open EulerNonuniqueness.Section2

def shapeChartRatio (point : ℝ × ℝ) : ℝ := rhombusRatio * (1 + point.1 + point.2)

def shapeChartAngle (point : ℝ × ℝ) : ℝ := Real.pi + Real.sqrt 2 * (point.1 - point.2)

def shapeChartVelocity (frequency : ℝ) (point : ℝ × ℝ) : ℝ × ℝ :=
  ((radialVelocity frequency (shapeChartRatio point) (shapeChartAngle point) / rhombusRatio +
      shapeAngleVelocity frequency (shapeChartRatio point) (shapeChartAngle point) / Real.sqrt 2) / 2,
    (radialVelocity frequency (shapeChartRatio point) (shapeChartAngle point) / rhombusRatio -
      shapeAngleVelocity frequency (shapeChartRatio point) (shapeChartAngle point) / Real.sqrt 2) / 2)

theorem shapeChartVelocity_zero (frequency : ℝ) : shapeChartVelocity frequency 0 = 0 := by
  simp [shapeChartVelocity, shapeChartRatio, shapeChartAngle, radialVelocity_at_rhombus,
    shapeAngleVelocity_at_rhombus]

theorem shapeChartVelocity_contDiffAt (frequency : ℝ) :
    ContDiffAt ℝ 2 (shapeChartVelocity frequency) 0 := by
  have ratioNonzero : rhombusRatio ≠ 0 := rhombusRatio_pos.ne'
  have ratioPositive := rhombusRatio_pos
  have denominatorNonzero : 1 + rhombusRatio ^ 2 + 2 * rhombusRatio ≠ 0 := by
    positivity
  unfold shapeChartVelocity radialVelocity shapeAngleVelocity shapeChartRatio shapeChartAngle
  fun_prop (disch := simp_all <;> positivity)

theorem fderiv_apply_of_partial_derivatives {function : ℝ × ℝ → ℝ}
    {first second firstDerivative secondDerivative : ℝ}
    (differentiable : DifferentiableAt ℝ function (first, second))
    (firstPartial : HasDerivAt (fun current => function (current, second)) firstDerivative first)
    (secondPartial : HasDerivAt (fun current => function (first, current)) secondDerivative second)
    (horizontal vertical : ℝ) :
    fderiv ℝ function (first, second) (horizontal, vertical) =
      horizontal * firstDerivative + vertical * secondDerivative := by
  have firstPath : HasDerivAt (fun current : ℝ => (current, second)) ((1 : ℝ), (0 : ℝ)) first :=
    (hasDerivAt_id first).prodMk (hasDerivAt_const first second)
  have secondPath : HasDerivAt (fun current : ℝ => (first, current)) ((0 : ℝ), (1 : ℝ)) second :=
    (hasDerivAt_const second first).prodMk (hasDerivAt_id second)
  have firstValue := (differentiable.hasFDerivAt.comp_hasDerivAt first firstPath).unique firstPartial
  have secondValue := (differentiable.hasFDerivAt.comp_hasDerivAt second secondPath).unique secondPartial
  have vectorIdentity : (horizontal, vertical) =
      horizontal • ((1 : ℝ), (0 : ℝ)) + vertical • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [vectorIdentity, map_add, map_smul, map_smul, firstValue, secondValue]
  rfl

theorem rawShapeVelocities_contDiffAt (frequency : ℝ) :
    ContDiffAt ℝ 2 (fun point : ℝ × ℝ => radialVelocity frequency point.1 point.2)
      (rhombusRatio, Real.pi) ∧
    ContDiffAt ℝ 2 (fun point : ℝ × ℝ => shapeAngleVelocity frequency point.1 point.2)
      (rhombusRatio, Real.pi) := by
  have ratioNonzero : rhombusRatio ≠ 0 := rhombusRatio_pos.ne'
  have ratioPositive := rhombusRatio_pos
  have denominatorNonzero : 1 + rhombusRatio ^ 2 + 2 * rhombusRatio ≠ 0 := by positivity
  constructor
  · unfold radialVelocity
    fun_prop (disch := simp_all <;> positivity)
  · unfold shapeAngleVelocity
    fun_prop (disch := simp_all <;> positivity)

theorem rawShapeVelocities_fderiv (frequency horizontal vertical : ℝ) :
    fderiv ℝ (fun point : ℝ × ℝ => radialVelocity frequency point.1 point.2)
      (rhombusRatio, Real.pi) (horizontal, vertical) = 2 * frequency * rhombusRatio * vertical ∧
    fderiv ℝ (fun point : ℝ × ℝ => shapeAngleVelocity frequency point.1 point.2)
      (rhombusRatio, Real.pi) (horizontal, vertical) = 4 * frequency / rhombusRatio * horizontal := by
  have smooth := rawShapeVelocities_contDiffAt frequency
  constructor
  · rw [fderiv_apply_of_partial_derivatives (smooth.1.differentiableAt (by norm_num))
      (radialVelocity_ratio_derivative frequency) (radialVelocity_phase_derivative frequency)]
    ring
  · rw [fderiv_apply_of_partial_derivatives (smooth.2.differentiableAt (by norm_num))
      (shapeAngleVelocity_ratio_derivative frequency) (shapeAngleVelocity_phase_derivative frequency)]
    ring

theorem shapeChartVelocity_directional_derivative (frequency horizontal vertical : ℝ) :
    HasDerivAt (fun time : ℝ => shapeChartVelocity frequency (horizontal * time, vertical * time))
      (2 * Real.sqrt 2 * frequency * horizontal, -(2 * Real.sqrt 2 * frequency) * vertical) 0 := by
  have ratioPath : HasDerivAt (fun time : ℝ => rhombusRatio * (1 + horizontal * time + vertical * time))
      (rhombusRatio * (horizontal + vertical)) 0 := by
    convert (((hasDerivAt_const 0 (1 : ℝ)).add ((hasDerivAt_id 0).const_mul horizontal)).add
      ((hasDerivAt_id 0).const_mul vertical)).const_mul rhombusRatio using 1 <;> simp
  have anglePath : HasDerivAt (fun time : ℝ => Real.pi + Real.sqrt 2 * (horizontal * time - vertical * time))
      (Real.sqrt 2 * (horizontal - vertical)) 0 := by
    convert (hasDerivAt_const 0 Real.pi).add
      ((((hasDerivAt_id 0).const_mul horizontal).sub ((hasDerivAt_id 0).const_mul vertical)).const_mul
        (Real.sqrt 2)) using 1 <;> simp
  have path : HasDerivAt (fun time : ℝ =>
      (rhombusRatio * (1 + horizontal * time + vertical * time),
        Real.pi + Real.sqrt 2 * (horizontal * time - vertical * time)))
      (rhombusRatio * (horizontal + vertical), Real.sqrt 2 * (horizontal - vertical)) 0 :=
    ratioPath.prodMk anglePath
  have smooth := rawShapeVelocities_contDiffAt frequency
  have radialBase : HasFDerivAt (fun point : ℝ × ℝ => radialVelocity frequency point.1 point.2)
      (fderiv ℝ (fun point : ℝ × ℝ => radialVelocity frequency point.1 point.2) (rhombusRatio, Real.pi))
      (rhombusRatio * (1 + horizontal * 0 + vertical * 0),
        Real.pi + Real.sqrt 2 * (horizontal * 0 - vertical * 0)) := by
    simpa using (smooth.1.differentiableAt (by norm_num)).hasFDerivAt
  have angularBase : HasFDerivAt (fun point : ℝ × ℝ => shapeAngleVelocity frequency point.1 point.2)
      (fderiv ℝ (fun point : ℝ × ℝ => shapeAngleVelocity frequency point.1 point.2) (rhombusRatio, Real.pi))
      (rhombusRatio * (1 + horizontal * 0 + vertical * 0),
        Real.pi + Real.sqrt 2 * (horizontal * 0 - vertical * 0)) := by
    simpa using (smooth.2.differentiableAt (by norm_num)).hasFDerivAt
  have radial := radialBase.comp_hasDerivAt (0 : ℝ) path
  have angular := angularBase.comp_hasDerivAt (0 : ℝ) path
  simp only [mul_zero, add_zero, sub_zero, mul_one] at radial angular
  rw [(rawShapeVelocities_fderiv frequency _ _).1] at radial
  rw [(rawShapeVelocities_fderiv frequency _ _).2] at angular
  have unstable := ((radial.div_const rhombusRatio).add (angular.div_const (Real.sqrt 2))).div_const 2
  have stable := ((radial.div_const rhombusRatio).sub (angular.div_const (Real.sqrt 2))).div_const 2
  have paired : HasDerivAt (fun time : ℝ => shapeChartVelocity frequency (horizontal * time, vertical * time))
      (((2 * frequency * rhombusRatio * (Real.sqrt 2 * (horizontal - vertical)) / rhombusRatio +
          4 * frequency / rhombusRatio * (rhombusRatio * (horizontal + vertical)) / Real.sqrt 2) / 2),
        ((2 * frequency * rhombusRatio * (Real.sqrt 2 * (horizontal - vertical)) / rhombusRatio -
          4 * frequency / rhombusRatio * (rhombusRatio * (horizontal + vertical)) / Real.sqrt 2) / 2)) 0 :=
    unstable.prodMk stable
  convert paired using 1
  ext <;> dsimp
  all_goals
    have ratioNonzero : rhombusRatio ≠ 0 := rhombusRatio_pos.ne'
    have sqrtTwoNonzero : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
    field_simp [ratioNonzero, sqrtTwoNonzero]
    ring_nf
    rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    ring

theorem shapeChartVelocity_fderiv (frequency horizontal vertical : ℝ) :
    fderiv ℝ (shapeChartVelocity frequency) 0 (horizontal, vertical) =
      (2 * Real.sqrt 2 * frequency * horizontal, -(2 * Real.sqrt 2 * frequency) * vertical) := by
  have path : HasDerivAt (fun time : ℝ => (horizontal * time, vertical * time)) (horizontal, vertical) 0 := by
    have first : HasDerivAt (fun time : ℝ => horizontal * time) horizontal 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul horizontal
    have second : HasDerivAt (fun time : ℝ => vertical * time) vertical 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul vertical
    exact first.prodMk second
  have base : HasFDerivAt (shapeChartVelocity frequency)
      (fderiv ℝ (shapeChartVelocity frequency) 0) (horizontal * 0, vertical * 0) := by
    simpa using ((shapeChartVelocity_contDiffAt frequency).differentiableAt (by norm_num)).hasFDerivAt
  have composed : HasDerivAt (fun time : ℝ => shapeChartVelocity frequency (horizontal * time, vertical * time))
      (fderiv ℝ (shapeChartVelocity frequency) 0 (horizontal, vertical)) 0 :=
    HasFDerivAt.comp_hasDerivAt (l := shapeChartVelocity frequency)
      (l' := fderiv ℝ (shapeChartVelocity frequency) 0) (0 : ℝ) base path
  exact composed.unique
    (shapeChartVelocity_directional_derivative frequency horizontal vertical)

theorem shapeChartVelocity_quadratic_remainder (frequency : ℝ) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ unstable stable : ℝ,
      |unstable| + |stable| < radius →
      |(shapeChartVelocity frequency (unstable, stable)).1 - 2 * Real.sqrt 2 * frequency * unstable| +
        |(shapeChartVelocity frequency (unstable, stable)).2 + 2 * Real.sqrt 2 * frequency * stable| ≤
          bound * (|unstable| + |stable|) ^ 2 := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    contDiffAt_quadratic_remainder (shapeChartVelocity_contDiffAt frequency)
  refine ⟨2 * bound, by positivity, radius, radiusPositive, ?_⟩
  intro unstable stable sizeBound
  have normBound : ‖(unstable, stable)‖ ≤ |unstable| + |stable| := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
  have pointEstimate := estimate (unstable, stable) (normBound.trans_lt sizeBound)
  rw [shapeChartVelocity_zero, sub_zero, shapeChartVelocity_fderiv] at pointEstimate
  have squaredBound : ‖(unstable, stable)‖ ^ 2 ≤ (|unstable| + |stable|) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) normBound 2
  have enlarged := pointEstimate.trans (mul_le_mul_of_nonneg_left squaredBound boundNonnegative)
  have firstBound := (norm_fst_le ((shapeChartVelocity frequency (unstable, stable)) -
    (2 * Real.sqrt 2 * frequency * unstable, -(2 * Real.sqrt 2 * frequency) * stable))).trans enlarged
  have secondBound := (norm_snd_le ((shapeChartVelocity frequency (unstable, stable)) -
    (2 * Real.sqrt 2 * frequency * unstable, -(2 * Real.sqrt 2 * frequency) * stable))).trans enlarged
  simp only [Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs, neg_mul, sub_neg_eq_add] at firstBound secondBound
  nlinarith

def shapeChart (ratio angle : ℝ) : ℝ × ℝ :=
  (((ratio / rhombusRatio - 1) + (angle - Real.pi) / Real.sqrt 2) / 2,
    ((ratio / rhombusRatio - 1) - (angle - Real.pi) / Real.sqrt 2) / 2)

theorem shapeChart_reconstruction (ratio angle : ℝ) :
    shapeChartRatio (shapeChart ratio angle) = ratio ∧
      shapeChartAngle (shapeChart ratio angle) = angle := by
  have ratioNonzero : rhombusRatio ≠ 0 := rhombusRatio_pos.ne'
  have sqrtTwoNonzero : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  constructor
  · unfold shapeChartRatio shapeChart
    dsimp
    field_simp [ratioNonzero, sqrtTwoNonzero]
    ring
  · unfold shapeChartAngle shapeChart
    dsimp
    field_simp [ratioNonzero, sqrtTwoNonzero]
    ring

theorem shapeChart_hasDerivAt {ratio angle : ℝ → ℝ} {frequency time : ℝ}
    (radialEquation : HasDerivAt ratio (radialVelocity frequency (ratio time) (angle time)) time)
    (angularEquation : HasDerivAt angle (shapeAngleVelocity frequency (ratio time) (angle time)) time) :
    HasDerivAt (fun currentTime => shapeChart (ratio currentTime) (angle currentTime))
      (shapeChartVelocity frequency (shapeChart (ratio time) (angle time))) time := by
  have horizontal := (radialEquation.div_const rhombusRatio).sub_const 1
  have vertical := (angularEquation.sub_const Real.pi).div_const (Real.sqrt 2)
  have first := (horizontal.add vertical).div_const 2
  have second := (horizontal.sub vertical).div_const 2
  have combined : HasDerivAt (fun currentTime => shapeChart (ratio currentTime) (angle currentTime))
      ((radialVelocity frequency (ratio time) (angle time) / rhombusRatio +
          shapeAngleVelocity frequency (ratio time) (angle time) / Real.sqrt 2) / 2,
        (radialVelocity frequency (ratio time) (angle time) / rhombusRatio -
          shapeAngleVelocity frequency (ratio time) (angle time) / Real.sqrt 2) / 2) time :=
    first.prodMk second
  simpa only [shapeChartVelocity, (shapeChart_reconstruction (ratio time) (angle time)).1,
    (shapeChart_reconstruction (ratio time) (angle time)).2] using combined

theorem shapeChartVelocity_frequency_scaling (frequency : ℝ) (point : ℝ × ℝ) :
    shapeChartVelocity frequency point = frequency • shapeChartVelocity 1 point := by
  unfold shapeChartVelocity radialVelocity shapeAngleVelocity
  ext <;> dsimp <;> simp only [smul_eq_mul, div_eq_mul_inv] <;> ring

theorem shapeChartVelocity_uniform_quadratic_remainder :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ frequency unstable stable : ℝ,
      |unstable| + |stable| < radius →
      |(shapeChartVelocity frequency (unstable, stable)).1 - 2 * Real.sqrt 2 * frequency * unstable| +
        |(shapeChartVelocity frequency (unstable, stable)).2 + 2 * Real.sqrt 2 * frequency * stable| ≤
          bound * |frequency| * (|unstable| + |stable|) ^ 2 := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    shapeChartVelocity_quadratic_remainder 1
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro frequency unstable stable sizeBound
  have firstIdentity : (shapeChartVelocity frequency (unstable, stable)).1 -
      2 * Real.sqrt 2 * frequency * unstable = frequency *
        ((shapeChartVelocity 1 (unstable, stable)).1 - 2 * Real.sqrt 2 * 1 * unstable) := by
    rw [shapeChartVelocity_frequency_scaling]
    change frequency * (shapeChartVelocity 1 (unstable, stable)).1 -
      2 * Real.sqrt 2 * frequency * unstable = _
    ring
  have secondIdentity : (shapeChartVelocity frequency (unstable, stable)).2 +
      2 * Real.sqrt 2 * frequency * stable = frequency *
        ((shapeChartVelocity 1 (unstable, stable)).2 + 2 * Real.sqrt 2 * 1 * stable) := by
    rw [shapeChartVelocity_frequency_scaling]
    change frequency * (shapeChartVelocity 1 (unstable, stable)).2 +
      2 * Real.sqrt 2 * frequency * stable = _
    ring
  rw [firstIdentity, secondIdentity, abs_mul, abs_mul, ← mul_add]
  have result := mul_le_mul_of_nonneg_left (estimate unstable stable sizeBound) (abs_nonneg frequency)
  nlinarith

end EulerNonuniqueness.Section6
