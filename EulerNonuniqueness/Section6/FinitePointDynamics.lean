import EulerNonuniqueness.Section6.FourPointLocalFlow

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

abbrev FinitePointConfiguration (Index : Type*) := Index → ℂ

def FinitePointNoncollision {Index : Type*} (positions : FinitePointConfiguration Index) : Prop :=
  ∀ target source, source ≠ target → positions target - positions source ≠ 0

def finitePointField {Index : Type*} [Fintype Index] [DecidableEq Index] (coefficients : Index → ℝ)
    (positions : FinitePointConfiguration Index) : FinitePointConfiguration Index :=
  fun target => Complex.I * ∑ source : Index,
    if source = target then 0 else (coefficients source : ℂ) / star (positions target - positions source)

theorem finitePointField_contDiffAt {Index : Type*} [Fintype Index] [DecidableEq Index] (coefficients : Index → ℝ)
    {positions : FinitePointConfiguration Index} (noncollision : FinitePointNoncollision positions) :
    ContDiffAt ℝ 2 (finitePointField coefficients) positions := by
  apply contDiffAt_pi.mpr
  intro target
  unfold finitePointField
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro source _
  by_cases same : source = target
  · simp only [same, if_true]
    exact contDiffAt_const
  · simp only [same, if_false]
    have difference : ContDiffAt ℝ 2
        (fun current : FinitePointConfiguration Index => current target - current source) positions := by fun_prop
    have conjugate : ContDiffAt ℝ 2
        (fun current : FinitePointConfiguration Index => star (current target - current source)) positions :=
      Complex.conjCLE.contDiff.contDiffAt.comp positions difference
    simpa only [div_eq_mul_inv] using
      contDiffAt_const.mul (conjugate.inv (star_ne_zero.mpr (noncollision target source same)))

theorem finitePointNoncollision_eventually {Index : Type*} [Fintype Index] {positions : FinitePointConfiguration Index}
    (noncollision : FinitePointNoncollision positions) :
    ∀ᶠ current in 𝓝 positions, FinitePointNoncollision current := by
  apply eventually_all.mpr
  intro target
  apply eventually_all.mpr
  intro source
  by_cases distinct : source ≠ target
  · have continuous : ContinuousAt (fun current : FinitePointConfiguration Index => current target - current source) positions := by
      fun_prop
    filter_upwards [continuous.eventually_ne (noncollision target source distinct)] with current currentNonzero
    exact fun _ => currentNonzero
  · exact Eventually.of_forall (by simp [distinct])

theorem finitePointField_local_solution {Index : Type*} [Fintype Index] [DecidableEq Index] (coefficients : Index → ℝ)
    {positions : FinitePointConfiguration Index} (noncollision : FinitePointNoncollision positions) :
    ∃ trajectory : ℝ → FinitePointConfiguration Index, trajectory 0 = positions ∧
      ∃ radius > (0 : ℝ), ∀ time ∈ Ioo (-radius) radius,
        FinitePointNoncollision (trajectory time) ∧
          HasDerivAt trajectory (finitePointField coefficients (trajectory time)) time := by
  have smooth : ContDiffAt ℝ 1 (finitePointField coefficients) positions :=
    (finitePointField_contDiffAt coefficients noncollision).of_le (by norm_num)
  obtain ⟨trajectory, initial, radius, radiusPositive, equation⟩ :=
    exists_forall_hasDerivAt_Ioo_eq_of_contDiffAt (0 : ℝ) smooth
  have zeroInside : (0 : ℝ) ∈ Ioo (0 - radius) (0 + radius) := by constructor <;> linarith
  have continuous : ContinuousAt trajectory 0 := (equation 0 zeroInside).continuousAt
  have collisionFree : ∀ᶠ time in 𝓝 (0 : ℝ), FinitePointNoncollision (trajectory time) :=
    continuous.tendsto.eventually (by simpa only [initial] using finitePointNoncollision_eventually noncollision)
  obtain ⟨collisionRadius, collisionRadiusPositive, collisionBall⟩ := Metric.mem_nhds_iff.mp collisionFree
  refine ⟨trajectory, initial, min radius collisionRadius, lt_min radiusPositive collisionRadiusPositive, ?_⟩
  intro time timeInside
  have radiusBound := min_le_left radius collisionRadius
  have collisionBound := min_le_right radius collisionRadius
  refine ⟨collisionBall ?_, equation time ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact abs_lt.mpr ⟨by linarith [timeInside.1], by linarith [timeInside.2]⟩
  · constructor <;> linarith [timeInside.1, timeInside.2]

theorem finitePointField_fourPoint_identity (coefficient : ℝ) (positions : FourPointConfiguration) :
    finitePointField (fun source => coefficient * fourPointSign source) positions = fourPointField coefficient positions := by
  funext target
  simp only [finitePointField, fourPointField, Complex.ofReal_mul]
  rw [mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro source _
  split_ifs <;> ring

end EulerNonuniqueness.Section6
