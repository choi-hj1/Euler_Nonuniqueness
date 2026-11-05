import EulerNonuniqueness.Section7.ReferenceOuterConfinement
import EulerNonuniqueness.Section3.HolderPaperBoundaryBound

noncomputable section

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000

theorem Scales.exists_uniform_reference_domain_support_radius (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {threshold constant : ℝ} (thresholdSmall : threshold ≤ 1 / 4) (constantNonnegative : 0 ≤ constant)
    (radiiSmall : ∀ index : ℕ, scales.radius index ≤ 1)
    (deformationSmall : ∀ index : ℕ, constant * (scales.omega index)⁻¹ ^ 2 ≤ 1) :
    ∃ supportRadius > (0 : ℝ), ∀ {count : ℕ}, 0 < count →
      ∀ {motion : PatchMotion count} {phase : Fin count → ℝ},
      ReferenceSolution scales motion phase threshold constant →
      ∀ time ∈ Icc (0 : ℝ) 2, ∀ index patch,
        motion.domain time index patch ⊆ closedBall 0 supportRadius := by
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ scales.hessian := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (scales.location_pos _).le _)
  have tailNonnegative : 0 ≤ ∑' source : ℕ, scales.circulation (source + 2) :=
    tsum_nonneg fun source => (scales.circulation_pos frequencyPositive ratioPositive _).le
  have lengthOnePositive := scales.length_pos 1
  have omegaOnePositive := scales.omega_pos frequencyPositive ratioPositive 1
  have outerNonnegative : 0 ≤ scales.outerDisplacementBound := by
    dsimp only [Scales.outerDisplacementBound]
    positivity
  let centerBound := constant * scales.outerDisplacementBound * scales.length 1 + 5
  let asymmetryBound := 2 * constant * scales.hessian * Real.exp (2 * constant * scales.strain)
  let supportRadius := 10 + constant * scales.outerDisplacementBound * scales.length 1 + asymmetryBound
  have centerNonnegative : 0 ≤ centerBound := by dsimp only [centerBound]; positivity
  have asymmetryNonnegative : 0 ≤ asymmetryBound := by dsimp only [asymmetryBound]; positivity
  refine ⟨supportRadius, by dsimp only [supportRadius]; positivity, ?_⟩
  intro count countPositive motion phase reference time member index patch
  obtain ⟨_, _, _, _, evolution, coarse, sharp⟩ := reference
  let outer : Fin count := ⟨0, countPositive⟩
  have data := coarse.2.1 time member index
  have outerCenter : ‖quadrupoleCenter motion time outer - (scales.location 1 : ℂ)‖ ≤
      constant * scales.outerDisplacementBound * scales.length 1 :=
    (div_le_iff₀ lengthOnePositive).mp (sharp.2 time member outer rfl)
  have relativeCenter : ‖quadrupoleCenter motion time index - quadrupoleCenter motion time outer‖ ≤ 4 := by
    by_cases same : index = outer
    · simp only [same, sub_self, norm_zero]; norm_num
    · have bound := (coarse.2.2 time member index outer same).2
      have indexIdentity : outer.val + 1 = 1 := rfl
      rw [indexIdentity] at bound
      have locationBound : |scales.location (index.val + 1) - scales.location 1| ≤ 2 := by
        exact abs_le.mpr ⟨by linarith [scales.location_pos (index.val + 1), scales.location_le_one 1],
          by linarith [scales.location_le_one (index.val + 1), scales.location_pos 1]⟩
      linarith
  have centerControl : ‖quadrupoleCenter motion time index - (0 : ℂ)‖ ≤ centerBound := by
    have identity : quadrupoleCenter motion time index =
        (quadrupoleCenter motion time index - quadrupoleCenter motion time outer) +
          (quadrupoleCenter motion time outer - (scales.location 1 : ℂ)) + (scales.location 1 : ℂ) := by ring
    have estimate := (norm_add_le
      ((quadrupoleCenter motion time index - quadrupoleCenter motion time outer) +
        (quadrupoleCenter motion time outer - (scales.location 1 : ℂ))) (scales.location 1 : ℂ)).trans
      (add_le_add_right ((norm_add_le _ _).trans (add_le_add relativeCenter outerCenter)) ‖(scales.location 1 : ℂ)‖)
    rw [← identity, Complex.norm_real, Real.norm_of_nonneg (scales.location_pos 1).le] at estimate
    simpa only [sub_zero, centerBound] using estimate.trans (by linarith [scales.location_le_one 1])
  have lengthPositive := scales.length_pos (index.val + 1)
  have lengthSmall := scales.length_le_one frequencyPositive ratioPositive (index.val + 1)
  have lower : scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference motion time index := by
    have actual := (le_div_iff₀ (sq_pos_of_pos lengthPositive)).mp data.2.2.1
    linarith
  have upper : diagonalDifference motion time index ≤ 2 * scales.length (index.val + 1) ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos lengthPositive)).mp data.2.2.2.1
  have radialUpper : radialShape motion time index ≤ 1 / 2 := by
    rw [radialShape_eq_unstable_add_stable]
    linarith [(le_abs_self _).trans data.1, (le_abs_self _).trans data.2.1]
  obtain ⟨positiveBound, negativeBound⟩ := halfDiagonals_norm_le_of_reference_shape lengthPositive
    ((by positivity : 0 < scales.length (index.val + 1) ^ 2 / 2).trans_le lower) upper radialUpper
  have timeNonnegative := member.1
  have timeBound := member.2
  have asymmetryControl : ‖centroidAsymmetry motion time index‖ ≤ asymmetryBound := by
    apply data.2.2.2.2.1.trans
    dsimp only [asymmetryBound]
    calc
      _ ≤ constant * scales.hessian * 1 ^ 2 * 2 * Real.exp (constant * scales.strain * 2) := by gcongr
      _ = _ := by ring
  have boundary (other : Fin 4) : BoundaryCloseToCircle scales motion time index other 1 := by
    obtain ⟨relabeling, periodic, relabelingBound, errorBound⟩ := data.2.2.2.2.2 other
    exact ⟨relabeling, periodic, relabelingBound, errorBound.mono (deformationSmall (index.val + 1))⟩
  intro position positionInside
  have positiveAbsolute : ‖positiveHalfDiagonal motion time index‖ ≤ 2 :=
    positiveBound.trans (by linarith)
  have negativeAbsolute : ‖negativeHalfDiagonal motion time index‖ ≤ 2 :=
    negativeBound.trans (by linarith)
  have estimate := evolution.reference_domain_confinement member index boundary
    (scales.radius_pos amplitudePositive frequencyPositive ratioPositive _)
    positiveAbsolute negativeAbsolute
    asymmetryControl centerControl patch position positionInside
  rw [mem_closedBall, dist_eq_norm, sub_zero]
  simp only [sub_zero] at estimate
  dsimp only [supportRadius, centerBound] at *
  linarith [radiiSmall (index.val + 1)]

end EulerNonuniqueness.Paper
