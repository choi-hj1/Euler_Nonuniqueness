import EulerNonuniqueness.Section5.SeparatingOrbitConstruction
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section2

def separatingRadiusScalarVelocity (rootRatio : ℝ) : ℝ :=
  Real.sqrt (2 * rootRatio * (rootRatio + 1)) * separatingEscapeVelocity 1 rootRatio +
    (2 * rootRatio + 1) / Real.sqrt (2 * rootRatio * (rootRatio + 1)) *
      ((1 / 4 : ℝ) * (1 - rootRatio ^ 2) / rootRatio ^ 2 *
        (rootRatio ^ 2 + 2 * rootRatio - 1) * Real.sqrt (rootRatio ^ 2 + 4 * rootRatio - 1))

private theorem radius_factor_hasDerivAt {rootRatio : ℝ} (positive : 0 < rootRatio) :
    HasDerivAt (fun value : ℝ => Real.sqrt (2 * value * (value + 1)))
      ((2 * rootRatio + 1) / Real.sqrt (2 * rootRatio * (rootRatio + 1))) rootRatio := by
  have radicalPositive : 0 < Real.sqrt (2 * rootRatio * (rootRatio + 1)) := by positivity
  convert (((hasDerivAt_id rootRatio).const_mul 2).mul ((hasDerivAt_id rootRatio).add_const 1)).sqrt
    (by positivity : 2 * rootRatio * (rootRatio + 1) ≠ 0) using 1
  field_simp
  ring

private theorem radius_product_identity (timeShift rotationPhase dipoleAngle time : ℝ) (offset : ℂ) :
    ‖(separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time -
      (separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time‖ =
      Real.sqrt (2 * separatingScalarOrbit 1 (by norm_num) (time + timeShift) *
        (separatingScalarOrbit 1 (by norm_num) (time + timeShift) + 1)) *
          separatingEscapeCoordinate 1 (by norm_num) (time + timeShift) := by
  let rootRatio := separatingScalarOrbit 1 (by norm_num) (time + timeShift)
  have bounds := separatingScalarOrbit_mem 1 (by norm_num) (time + timeShift)
  have rootPositive : 0 < rootRatio := by
    dsimp only [rootRatio]
    linarith only [bounds.1, sqrt_two_gt_one]
  have endpointPositive : 0 < 1 - rootRatio ^ 2 := by
    have belowOne : rootRatio < 1 := bounds.2
    nlinarith only [belowOne, rootPositive]
  have radiusSquare := (separating_pair_distance_squares 1 (by norm_num) (time + timeShift)).2
  have factorSquare := Real.sq_sqrt (show 0 ≤ 2 * rootRatio * (rootRatio + 1) by positivity)
  have radicalSquare := Real.sq_sqrt endpointPositive.le
  have productSquare : (Real.sqrt (2 * rootRatio * (rootRatio + 1)) *
      (Real.sqrt (1 - rootRatio ^ 2))⁻¹) ^ 2 = 2 * rootRatio / (1 - rootRatio) := by
    rw [mul_pow, inv_pow, factorSquare, radicalSquare]
    have belowOne : rootRatio < 1 := bounds.2
    field_simp [(sub_pos.mpr belowOne).ne', endpointPositive.ne']
    ring
  have radiusIdentity : ‖(separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time -
      (separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time‖ =
        ‖separatingPositive 1 (by norm_num) (time + timeShift) -
          separatingNegative 1 (by norm_num) (time + timeShift)‖ := by
    simp only [separatingCandidate, ← mul_sub, norm_mul, separatingCandidate_rotation_norm, one_mul]
  rw [radiusIdentity]
  dsimp only [separatingEscapeCoordinate]
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp (radiusSquare.trans productSquare.symm)

private theorem scalar_velocity_escape_product {rootRatio : ℝ}
    (positive : 0 < rootRatio) (belowOne : rootRatio < 1) :
    separatingScalarVelocity 1 rootRatio * (Real.sqrt (1 - rootRatio ^ 2))⁻¹ =
      (1 / 4 : ℝ) * (1 - rootRatio ^ 2) / rootRatio ^ 2 *
        (rootRatio ^ 2 + 2 * rootRatio - 1) * Real.sqrt (rootRatio ^ 2 + 4 * rootRatio - 1) := by
  have endpointPositive : 0 < 1 - rootRatio ^ 2 := by nlinarith only [positive, belowOne]
  have radicalPositive := Real.sqrt_pos.mpr endpointPositive
  have radicalSquare := Real.sq_sqrt endpointPositive.le
  have radicalCube : Real.sqrt (1 - rootRatio ^ 2) ^ 3 =
      (1 - rootRatio ^ 2) * Real.sqrt (1 - rootRatio ^ 2) := by
    calc
      _ = Real.sqrt (1 - rootRatio ^ 2) ^ 2 * Real.sqrt (1 - rootRatio ^ 2) := by ring
      _ = _ := by rw [radicalSquare]
  unfold separatingScalarVelocity
  rw [radicalCube]
  field_simp [positive.ne', radicalPositive.ne']
  ring

private theorem radius_scalar_velocity_positive {rootRatio : ℝ}
    (aboveRhombus : Real.sqrt 2 - 1 < rootRatio) (belowOne : rootRatio < 1) :
    0 < separatingRadiusScalarVelocity rootRatio := by
  have rootPositive : 0 < rootRatio := by linarith only [aboveRhombus, sqrt_two_gt_one]
  have firstPositive : 0 < rootRatio ^ 2 + 2 * rootRatio - 1 := by
    have productPositive := mul_pos (sub_pos.mpr aboveRhombus)
      (show 0 < rootRatio + Real.sqrt 2 + 1 by linarith only [rootPositive, sqrt_two_gt_one])
    nlinarith only [productPositive, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have secondPositive : 0 < rootRatio ^ 2 + 4 * rootRatio - 1 := by
    linarith only [firstPositive, rootPositive]
  have endpointPositive : 0 < 1 - rootRatio ^ 2 := by nlinarith only [rootPositive, belowOne]
  dsimp only [separatingRadiusScalarVelocity, separatingEscapeVelocity]
  positivity

theorem separatingCandidate_radius_dynamics (timeShift rotationPhase dipoleAngle : ℝ) (offset : ℂ) :
    let radius := fun time => ‖(separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time -
      (separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time‖
    let velocity := fun time => separatingRadiusScalarVelocity (separatingScalarOrbit 1 (by norm_num) (time + timeShift))
    (∀ time : ℝ, HasDerivAt radius (velocity time) time) ∧ StrictMono radius ∧
      Tendsto velocity atTop (𝓝 2) ∧ ∀ᶠ time : ℝ in atTop, 1 ≤ velocity time := by
  dsimp only
  have derivative (time : ℝ) : HasDerivAt
      (fun current => ‖(separatingCandidate timeShift rotationPhase dipoleAngle offset).positive current -
        (separatingCandidate timeShift rotationPhase dipoleAngle offset).negative current‖)
      (separatingRadiusScalarVelocity (separatingScalarOrbit 1 (by norm_num) (time + timeShift))) time := by
    let rootRatio := separatingScalarOrbit 1 (by norm_num) (time + timeShift)
    have bounds := separatingScalarOrbit_mem 1 (by norm_num) (time + timeShift)
    have rootPositive : 0 < rootRatio := by
      dsimp only [rootRatio]
      linarith only [bounds.1, sqrt_two_gt_one]
    have scalarDerivative := (separatingScalarOrbit_hasDerivAt 1 (by norm_num) (time + timeShift)).comp
      time ((hasDerivAt_id time).add_const timeShift)
    have factorDerivative := (radius_factor_hasDerivAt rootPositive).comp time scalarDerivative
    have escapeDerivative := (separatingEscapeCoordinate_trajectory_hasDerivAt 1 (by norm_num) (time + timeShift)).comp
      time ((hasDerivAt_id time).add_const timeShift)
    have productDerivative := (factorDerivative.mul escapeDerivative).congr_of_eventuallyEq
      (Eventually.of_forall (fun current => radius_product_identity timeShift rotationPhase dipoleAngle current offset))
    convert productDerivative using 1
    simp only [Function.comp_def, id_eq, one_mul, mul_one, separatingRadiusScalarVelocity, separatingEscapeCoordinate]
    rw [show (2 * rootRatio + 1) / Real.sqrt (2 * rootRatio * (rootRatio + 1)) *
        separatingScalarVelocity 1 rootRatio * (Real.sqrt (1 - rootRatio ^ 2))⁻¹ =
      (2 * rootRatio + 1) / Real.sqrt (2 * rootRatio * (rootRatio + 1)) *
        (separatingScalarVelocity 1 rootRatio * (Real.sqrt (1 - rootRatio ^ 2))⁻¹) by ring,
      scalar_velocity_escape_product rootPositive bounds.2]
    ring
  have strictlyIncreasing : StrictMono (fun time =>
      ‖(separatingCandidate timeShift rotationPhase dipoleAngle offset).positive time -
        (separatingCandidate timeShift rotationPhase dipoleAngle offset).negative time‖) := by
    apply strictMono_of_deriv_pos
    intro time
    rw [(derivative time).deriv]
    have bounds := separatingScalarOrbit_mem 1 (by norm_num) (time + timeShift)
    exact radius_scalar_velocity_positive bounds.1 bounds.2
  have scalarLimit : Tendsto (fun time : ℝ => separatingScalarOrbit 1 (by norm_num) (time + timeShift)) atTop (𝓝 1) :=
    (separatingScalarOrbit_outgoing_limit 1 (by norm_num)).comp
      (tendsto_atTop_add_const_right _ _ tendsto_id)
  have velocityContinuous : ContinuousAt separatingRadiusScalarVelocity 1 := by
    unfold separatingRadiusScalarVelocity separatingEscapeVelocity
    fun_prop (disch := norm_num)
  have velocityAtOne : separatingRadiusScalarVelocity 1 = 2 := by
    norm_num [separatingRadiusScalarVelocity, separatingEscapeVelocity]
  have velocityLimit := velocityContinuous.tendsto.comp scalarLimit
  rw [velocityAtOne] at velocityLimit
  exact ⟨derivative, strictlyIncreasing, velocityLimit,
    (velocityLimit.eventually (eventually_gt_nhds (by norm_num : (1 : ℝ) < 2))).mono (fun _ positive => positive.le)⟩

end EulerNonuniqueness.Paper
