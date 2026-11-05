import EulerNonuniqueness.Section4.ReferencePairwiseDomainGap
import EulerNonuniqueness.Section4.ReferenceInitialInvariants
import EulerNonuniqueness.Section6.MovingQuadrupoleMemoryHistory
import EulerNonuniqueness.Section1.ForeignInteractionWeight

noncomputable section

open Set MeasureTheory
open scoped Topology NNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

theorem reference_centroidAsymmetry_bound {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {horizon finish error threshold : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (horizonPositive : 0 < horizon) (finishNonnegative : 0 ≤ finish)
    (timeRange : Icc 0 finish ⊆ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {phase unstable : Fin count → ℝ}
    (initial : ReferenceInitialDisks scales family.patchMotion phase unstable threshold)
    (inside : ∀ time ∈ Icc 0 finish, ∀ index,
      time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ time ∈ Icc 0 finish, ∀ index label,
      (family.patch index).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (differenceLower : ∀ time ∈ Icc 0 finish, ∀ index : Fin count,
      scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion time index)
    (differenceUpper : ∀ time ∈ Icc 0 finish, ∀ index : Fin count,
      diagonalDifference family.patchMotion time index ≤ 2 * scales.length (index.val + 1) ^ 2)
    (radialSmall : ∀ time ∈ Icc 0 finish, ∀ index, |radialShape family.patchMotion time index| ≤ 1 / 2)
    (asymmetrySmall : ∀ time ∈ Icc 0 finish, ∀ index,
      ‖centroidAsymmetry family.patchMotion time index‖ ≤ scales.length (index.val + 1) / 64)
    (centerSeparation : ∀ time ∈ Icc 0 finish, ∀ receiver source : Fin count, receiver ≠ source →
      |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 ≤
        ‖quadrupoleCenter family.patchMotion time receiver - quadrupoleCenter family.patchMotion time source‖)
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (boundaryControl : ∀ time ∈ Icc 0 finish, ∀ index patch,
      BoundaryCloseToCircle scales family.patchMotion time index patch error)
    (radiusSmall : ∀ index : Fin count,
      scales.radius (index.val + 1) * (1 + error) ≤ scales.length (index.val + 1) / 32)
    (index : Fin count) :
    ∀ time ∈ Icc 0 finish,
      ‖centroidAsymmetry family.patchMotion time index‖ ≤
        (497664 / Real.pi) * scales.hessian * scales.length (index.val + 1) ^ 2 * time *
          Real.exp ((1152 / Real.pi) * scales.strain * time) := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have lengthPositive := scales.length_pos (index.val + 1)
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ scales.hessian := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (scales.location_pos _).le _)
  let strain : ℝ≥0 := ⟨(1152 / Real.pi) * scales.strain, by positivity⟩
  let hessian := (55296 / Real.pi) * scales.hessian
  let radius := 3 * scales.length (index.val + 1)
  let center := fun time => quadrupoleCenter family.patchMotion time index
  let distance := fun (_ : ℝ) (source : Fin count) =>
    |scales.location (index.val + 1) - scales.location (source.val + 1)| / 8
  let region := fun time => Metric.ball (center time) (scales.length (index.val + 1))
  have lengthWeaker (source : Fin count) :
      scales.length (source.val + 1) ≤ scales.location (source.val + 1) / 100 := by
    linarith [lengthSmall source, scales.location_pos (source.val + 1)]
  have domainBound (time : ℝ) (member : time ∈ Icc 0 finish) (patch : Fin 4) :
      family.patchMotion.domain time index patch ⊆ Metric.closedBall (center time) radius := by
    have lengthPositive := scales.length_pos (index.val + 1)
    have differencePositive : 0 < diagonalDifference family.patchMotion time index :=
      (by positivity : 0 < scales.length (index.val + 1) ^ 2 / 2).trans_le (differenceLower time member index)
    obtain ⟨positiveBound, negativeBound⟩ := halfDiagonals_norm_le_of_reference_shape lengthPositive
      differencePositive (differenceUpper time member index) ((le_abs_self _).trans (radialSmall time member index))
    intro position positionInside
    have centerControl : ‖quadrupoleCenter family.patchMotion time index - center time‖ ≤ (0 : ℝ) := by simp [center]
    have bound := evolution.reference_domain_confinement (timeRange member) index (boundaryControl time member index)
      (scales.radius_pos amplitudePositive frequencyPositive ratioPositive _) positiveBound negativeBound
      (asymmetrySmall time member index) centerControl patch position positionInside
    rw [Metric.mem_closedBall, dist_eq_norm]
    dsimp only [radius]
    linarith [radiusSmall index]
  have positive (time : ℝ) (member : time ∈ Icc 0 finish) (source : Fin count)
      (different : source ∈ Finset.univ.erase index) : 0 < distance time source := by
    apply div_pos _ (by norm_num)
    apply scales.location_distance_pos
    intro equality
    exact (Finset.mem_erase.mp different).1 (Fin.ext (Nat.add_right_cancel equality).symm)
  have separated (time : ℝ) (member : time ∈ Icc 0 finish) (position : ℂ)
      (positionInside : position ∈ region time) (source : Fin count)
      (different : source ∈ Finset.univ.erase index) (patch : Fin 4) (location : ℂ)
      (locationInside : location ∈ family.patchMotion.domain time source patch) :
      distance time source ≤ ‖position - location‖ := by
    have sourceDifferent : index ≠ source := Ne.symm (Finset.mem_erase.mp different).1
    have indexDifferent : index.val + 1 ≠ source.val + 1 :=
      fun equality => sourceDifferent (Fin.ext (Nat.add_right_cancel equality))
    have receiverControl : ‖position - center time‖ ≤ scales.location (index.val + 1) / 16 := by
      have near : ‖position - center time‖ < scales.length (index.val + 1) := by
        simpa only [region, Metric.mem_ball, dist_eq_norm] using positionInside
      linarith [lengthSmall index, scales.location_pos (index.val + 1)]
    exact scales.foreign_moving_point_separation indexDifferent (centerSeparation time member index source sourceDifferent)
      receiverControl (evolution.reference_domain_moving_offset_bound (timeRange member) source
        (differenceLower time member source) (differenceUpper time member source) (radialSmall time member source)
        (asymmetrySmall time member source) (lengthWeaker source) (boundaryControl time member source)
        (scales.radius_pos amplitudePositive frequencyPositive ratioPositive _) (radiusSmall source)
        patch location locationInside)
  have near (time : ℝ) (member : time ∈ Icc 0 finish) (source : Fin count)
      (different : source ∈ Finset.univ.erase index) : 2 * radius ≤ distance time source := by
    have locations := scales.location_sum_le_three_distance
      (show index.val + 1 ≠ source.val + 1 from fun equality =>
        (Finset.mem_erase.mp different).1 (Fin.ext (Nat.add_right_cancel equality).symm))
    dsimp only [radius, distance]
    linarith [lengthSmall index, scales.location_pos (source.val + 1)]
  have history := family.centroidAsymmetry_memory_history_bound (hessian := hessian) (strain := strain)
    scales densityEquation (fun _ => radius) continuous_const
    finishNonnegative evolution horizonPositive timeRange amplitudePositive frequencyPositive ratioPositive inside material
    index center (fun _ _ => by dsimp only [radius]; positivity)
    domainBound distance region (fun _ _ => Metric.ball_mem_nhds _ (scales.length_pos _))
    positive separated near (fun _ _ => scales.foreign_strain_weight_le frequencyBound ratioBound alphaPositive index)
    (fun _ _ => scales.foreign_hessian_weight_le frequencyBound ratioBound alphaPositive index)
  have initialZero := (evolution.reference_initial_center_and_asymmetry horizonPositive.le amplitudePositive frequencyPositive
    ratioPositive initial index).2
  intro time member
  have integrandContinuous : Continuous (fun current : ℝ => Real.exp (-(strain : ℝ) * current) * (hessian * radius ^ 2)) := by
    fun_prop
  have integralBound : (∫ current in (0 : ℝ)..time, Real.exp (-(strain : ℝ) * current) * (hessian * radius ^ 2)) ≤
      time * (hessian * radius ^ 2) := by
    have estimate := intervalIntegral.integral_mono_on member.1 (integrandContinuous.intervalIntegrable 0 time)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => hessian * radius ^ 2) volume 0 time)
      (fun current currentInside => mul_le_of_le_one_left (by dsimp only [hessian]; positivity)
        (Real.exp_le_one_iff.mpr (by
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr strain.property) currentInside.1)))
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using estimate
  have estimate := history time member
  rw [initialZero, norm_zero, zero_add] at estimate
  apply (estimate.trans (mul_le_mul_of_nonneg_left integralBound (Real.exp_pos _).le)).trans_eq
  dsimp only [strain, hessian, radius]
  simp only [NNReal.coe_mk]
  ring_nf

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
