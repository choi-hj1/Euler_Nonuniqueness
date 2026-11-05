import EulerNonuniqueness.Section3.MovingCentroidGaugeField

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance movingStateGeometryHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance movingStateGeometryC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

def FiniteContourConfiguration.movingStateAdmissible {count : ℕ}
    (configuration : FiniteContourConfiguration count) (centerBound shapeRadius gap : ℝ) : Set (MovingContourState count) :=
  {state | (∀ index, ‖state.2.1 index‖ ≤ centerBound) ∧
    (∀ index, ‖state.2.2 index - standardCircleBanach‖ ≤ shapeRadius) ∧
    ∀ first second, first ≠ second →
      3 * (configuration.radius first + configuration.radius second) + gap ≤ ‖state.2.1 first - state.2.1 second‖}

def FiniteContourConfiguration.movingPhysicalUniformBound {count : ℕ}
    (configuration : FiniteContourConfiguration count) (centerBound : ℝ) : ℝ :=
  centerBound + 3 * ∑ index, configuration.radius index

def FiniteContourConfiguration.movingPhysicalLipschitzConstant {count : ℕ}
    (configuration : FiniteContourConfiguration count) (index : Fin count) : ℝ :=
  1 + configuration.radius index * (1 + 3 * |configuration.density index / 2|)

theorem movingContourState_time_norm_sub_le {count : ℕ} (first second : MovingContourState count) :
    ‖first.1 - second.1‖ ≤ ‖first - second‖ := norm_fst_le (first - second)

theorem movingContourState_center_norm_sub_le {count : ℕ} (first second : MovingContourState count) (index : Fin count) :
    ‖first.2.1 index - second.2.1 index‖ ≤ ‖first - second‖ :=
  (norm_le_pi_norm (first.2.1 - second.2.1) index).trans
    ((norm_fst_le (first.2 - second.2)).trans (norm_snd_le (first - second)))

theorem movingContourState_shape_norm_sub_le {count : ℕ} (first second : MovingContourState count) (index : Fin count) :
    ‖first.2.2 index - second.2.2 index‖ ≤ ‖first - second‖ :=
  (norm_le_pi_norm (first.2.2 - second.2.2) index).trans
    ((norm_snd_le (first.2 - second.2)).trans (norm_snd_le (first - second)))

theorem unitRotationC1_parameter_norm_bound (firstPhase secondPhase : Circle)
    (first second : PeriodicC1HolderHalf) :
    ‖(firstPhase : ℂ) • first - (secondPhase : ℂ) • second‖ ≤
      ‖first - second‖ + ‖(firstPhase : ℂ) - (secondPhase : ℂ)‖ * ‖second‖ := by
  have identity : (firstPhase : ℂ) • first - (secondPhase : ℂ) • second =
      (firstPhase : ℂ) • (first - second) + ((firstPhase : ℂ) - (secondPhase : ℂ)) • second := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change (firstPhase : ℂ) * first.val.1 label - (secondPhase : ℂ) * second.val.1 label =
      (firstPhase : ℂ) * (first.val.1 label - second.val.1 label) +
        ((firstPhase : ℂ) - (secondPhase : ℂ)) * second.val.1 label
    ring
  rw [identity]
  apply (norm_add_le ((firstPhase : ℂ) • (first - second)) (((firstPhase : ℂ) - (secondPhase : ℂ)) • second)).trans
  rw [unitRotationC1_norm]
  have scaleNorm : ‖((firstPhase : ℂ) - (secondPhase : ℂ)) • second‖ =
      ‖(firstPhase : ℂ) - (secondPhase : ℂ)‖ * ‖second‖ := by
    change ‖((firstPhase : ℂ) - (secondPhase : ℂ)) • second.val‖ = _
    exact norm_smul ((firstPhase : ℂ) - (secondPhase : ℂ)) second.val
  rw [scaleNorm]

theorem FiniteContourConfiguration.movingStatePhase_parameter_norm_bound {count : ℕ}
    (configuration : FiniteContourConfiguration count) (first second : MovingContourState count) (index : Fin count) :
    ‖(configuration.movingStatePhase first index : ℂ) - (configuration.movingStatePhase second index : ℂ)‖ ≤
      |configuration.density index / 2| * ‖first - second‖ := by
  have actual := (circle_rotation_lipschitz (configuration.density index / 2)).dist_le_mul first.1 second.1
  change dist (configuration.movingStatePhase first index : ℂ) (configuration.movingStatePhase second index : ℂ) ≤ _ at actual
  rw [dist_eq_norm, dist_eq_norm] at actual
  exact actual.trans (mul_le_mul_of_nonneg_left (movingContourState_time_norm_sub_le first second) (abs_nonneg _))

theorem FiniteContourConfiguration.movingStatePhysicalContour_parameter_norm_bound {count : ℕ}
    (configuration : FiniteContourConfiguration count) (first second : MovingContourState count)
    (secondBounded : ∀ index, ‖second.2.2 index‖ ≤ 3) (index : Fin count) :
    ‖configuration.movingStatePhysicalContour first index - configuration.movingStatePhysicalContour second index‖ ≤
      configuration.movingPhysicalLipschitzConstant index * ‖first - second‖ := by
  have rotationBound := unitRotationC1_parameter_norm_bound
    (configuration.movingStatePhase first index) (configuration.movingStatePhase second index)
    (first.2.2 index) (second.2.2 index)
  have phaseBound := configuration.movingStatePhase_parameter_norm_bound first second index
  have shapeBound := movingContourState_shape_norm_sub_le first second index
  have rotated : ‖(configuration.movingStatePhase first index : ℂ) • first.2.2 index -
      (configuration.movingStatePhase second index : ℂ) • second.2.2 index‖ ≤
      (1 + 3 * |configuration.density index / 2|) * ‖first - second‖ := by
    have productBound := mul_le_mul phaseBound (secondBounded index) (norm_nonneg _) (by positivity)
    nlinarith
  have identity : configuration.movingStatePhysicalContour first index - configuration.movingStatePhysicalContour second index =
      (c1Constant (first.2.1 index) - c1Constant (second.2.1 index)) + configuration.radius index •
        ((configuration.movingStatePhase first index : ℂ) • first.2.2 index -
          (configuration.movingStatePhase second index : ℂ) • second.2.2 index) := by
    unfold FiniteContourConfiguration.movingStatePhysicalContour c1AffineContour
    rw [smul_sub (configuration.radius index)
      ((configuration.movingStatePhase first index : ℂ) • first.2.2 index)
      ((configuration.movingStatePhase second index : ℂ) • second.2.2 index)]
    abel
  rw [identity]
  have centerBound := (c1Constant_difference_norm_bound (first.2.1 index) (second.2.1 index)).trans
    (movingContourState_center_norm_sub_le first second index)
  have scaleBound : ‖configuration.radius index •
        ((configuration.movingStatePhase first index : ℂ) • first.2.2 index -
          (configuration.movingStatePhase second index : ℂ) • second.2.2 index)‖ ≤
      configuration.radius index * ((1 + 3 * |configuration.density index / 2|) * ‖first - second‖) := by
    rw [norm_smul (configuration.radius index)
      ((configuration.movingStatePhase first index : ℂ) • first.2.2 index -
        (configuration.movingStatePhase second index : ℂ) • second.2.2 index), Real.norm_eq_abs,
      abs_of_pos (configuration.radius_pos index)]
    exact mul_le_mul_of_nonneg_left rotated (configuration.radius_pos index).le
  apply (norm_add_le (c1Constant (first.2.1 index) - c1Constant (second.2.1 index))
    (configuration.radius index • ((configuration.movingStatePhase first index : ℂ) • first.2.2 index -
      (configuration.movingStatePhase second index : ℂ) • second.2.2 index))).trans
  exact (add_le_add centerBound scaleBound).trans_eq (by unfold FiniteContourConfiguration.movingPhysicalLipschitzConstant; ring)

theorem FiniteContourConfiguration.movingStatePhysicalContour_norm_bound {count : ℕ}
    (configuration : FiniteContourConfiguration count) (state : MovingContourState count)
    {centerBound : ℝ} (centersBounded : ∀ index, ‖state.2.1 index‖ ≤ centerBound)
    (shapesBounded : ∀ index, ‖state.2.2 index‖ ≤ 3) (index : Fin count) :
    ‖configuration.movingStatePhysicalContour state index‖ ≤ configuration.movingPhysicalUniformBound centerBound := by
  have radiusBound : configuration.radius index ≤ ∑ other, configuration.radius other :=
    Finset.single_le_sum (fun other _ => (configuration.radius_pos other).le) (Finset.mem_univ index)
  have actual := c1AffineContour_norm_bound (state.2.1 index) (configuration.radius index)
    ((configuration.movingStatePhase state index : ℂ) • state.2.2 index)
  rw [unitRotationC1_norm, abs_of_pos (configuration.radius_pos index)] at actual
  unfold FiniteContourConfiguration.movingPhysicalUniformBound FiniteContourConfiguration.movingStatePhysicalContour
  have productBound := mul_le_mul_of_nonneg_left (shapesBounded index) (configuration.radius_pos index).le
  linarith [centersBounded index]

end EulerNonuniqueness.Paper
