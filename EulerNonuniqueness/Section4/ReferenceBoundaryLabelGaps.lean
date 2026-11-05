import EulerNonuniqueness.Section4.ReferencePatchDomainSeparation
import EulerNonuniqueness.Section4.ReferencePairwiseDomainGap
import EulerNonuniqueness.Section1.UniformScaleBounds
import EulerNonuniqueness.Section1.ExternalFieldScaleBounds
import EulerNonuniqueness.Section1.UniformInitialScaleSmallness
import EulerNonuniqueness.Section3.HolderPaperBoundaryBound

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000

theorem reference_boundary_label_gap_of_shape_geometry {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ)
    (radiusPositive : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
    (differenceLower : ∀ index : Fin count, scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference motion time index)
    (differenceUpper : ∀ index : Fin count, diagonalDifference motion time index ≤ 2 * scales.length (index.val + 1) ^ 2)
    (radialSmall : ∀ index, |radialShape motion time index| ≤ 1 / 2)
    (asymmetrySmall : ∀ index, ‖centroidAsymmetry motion time index‖ ≤ scales.length (index.val + 1) / 64)
    (centerSeparation : ∀ receiver source : Fin count, receiver ≠ source →
      |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 ≤
        ‖quadrupoleCenter motion time receiver - quadrupoleCenter motion time source‖)
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (radiusSmall : ∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 10000)
    (control : ∀ index patch, BoundaryCloseToCircle scales motion time index patch 1)
    (receiver source : Fin count) (first second : Fin 4) (different : (receiver, first) ≠ (source, second)) :
    8 * scales.radius (receiver.val + 1) + 8 * scales.radius (source.val + 1) <
      dist (motion.boundary time receiver first 0) (motion.boundary time source second 0) := by
  have labelBound (index : Fin count) (patch : Fin 4) :
      dist (motion.boundary time index patch 0) (patchCentroid motion time index patch) ≤ 2 * scales.radius (index.val + 1) := by
    simpa only [dist_eq_norm, one_add_one_eq_two, mul_comm] using
      (control index patch).boundary_distance_le (radiusPositive index) 0
  have triangle : dist (patchCentroid motion time receiver first) (patchCentroid motion time source second) ≤
      2 * scales.radius (receiver.val + 1) +
        dist (motion.boundary time receiver first 0) (motion.boundary time source second 0) + 2 * scales.radius (source.val + 1) := by
    have firstTriangle := dist_triangle (patchCentroid motion time receiver first)
      (motion.boundary time receiver first 0) (patchCentroid motion time source second)
    have secondTriangle := dist_triangle (motion.boundary time receiver first 0)
      (motion.boundary time source second 0) (patchCentroid motion time source second)
    have firstBound := labelBound receiver first
    have secondBound := labelBound source second
    rw [dist_comm (motion.boundary time receiver first 0) (patchCentroid motion time receiver first)] at firstBound
    linarith only [firstTriangle, secondTriangle, firstBound, secondBound]
  by_cases same : receiver = source
  · subst source
    have patchesDifferent : first ≠ second := fun equality => different (Prod.ext rfl equality)
    have centerBound := patchCentroid_pair_lower_of_reference_shape motion time receiver (scales.length_pos _)
      (differenceLower receiver) (radialSmall receiver) (asymmetrySmall receiver) first second patchesDifferent
    rw [← dist_eq_norm] at centerBound
    linarith only [centerBound, triangle, radiusSmall receiver, scales.length_pos (receiver.val + 1)]
  · have indexDifferent : receiver.val + 1 ≠ source.val + 1 :=
      fun equality => same (Fin.ext (Nat.add_right_cancel equality))
    have lengthWeaker (index : Fin count) : scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 100 := by
      linarith [lengthSmall index, scales.location_pos (index.val + 1)]
    have centerBound := scales.foreign_moving_point_separation indexDifferent (centerSeparation receiver source same)
      (reference_centroid_moving_offset_bound scales motion time receiver (differenceLower receiver) (differenceUpper receiver)
        (radialSmall receiver) (asymmetrySmall receiver) (lengthWeaker receiver) first)
      (reference_centroid_moving_offset_bound scales motion time source (differenceLower source) (differenceUpper source)
        (radialSmall source) (asymmetrySmall source) (lengthWeaker source) second)
    rw [← dist_eq_norm] at centerBound
    have locations := scales.location_sum_le_three_distance indexDifferent
    have locationPositive := scales.location_distance_pos indexDifferent
    linarith only [centerBound, triangle, locations, locationPositive, radiusSmall receiver, radiusSmall source,
      lengthSmall receiver, lengthSmall source]

theorem Scales.eventually_reference_coarse_boundary_label_gaps (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {threshold constant : ℝ} (thresholdSmall : threshold ≤ 1 / 8) (constantNonnegative : 0 ≤ constant) :
    ∀ᶠ frequency : ℝ in atTop,
      let changed : Scales := {scales with frequency := frequency}
      ∀ {count : ℕ} (motion : PatchMotion count), ReferenceCoarseBounds changed motion threshold constant →
        ∀ time ∈ Icc (0 : ℝ) 2, ∀ receiver source : Fin count, ∀ first second : Fin 4,
          (receiver, first) ≠ (source, second) →
          8 * changed.radius (receiver.val + 1) + 8 * changed.radius (source.val + 1) <
            dist (motion.boundary time receiver first 0) (motion.boundary time source second 0) := by
  have tolerancePositive : 0 < 1 / (256 * (constant + 1) * Real.exp (2 * constant)) := by positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop constant,
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 1000),
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1 / 10000),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds tolerancePositive)]
    with frequency frequencyBound constantBound lengths radii strainSmall hessianSmall
  dsimp only
  intro count motion coarse time timeInside receiver source first second different
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun index =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun index =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
  have timeNonnegative := timeInside.1
  have timeBound := timeInside.2
  have exponentBound : constant * changed.strain * time ≤ 2 * constant := by
    calc
      _ ≤ constant * 1 * 2 := by gcongr
      _ = _ := by ring
  have memoryBound : 2 * constant * changed.hessian * Real.exp (2 * constant) ≤ 1 / 64 := by
    have multiplied := (le_div_iff₀ (by positivity : 0 < 256 * (constant + 1) * Real.exp (2 * constant))).mp hessianSmall.le
    have productNonnegative : 0 ≤ changed.hessian * Real.exp (2 * constant) := by positivity
    nlinarith only [multiplied, productNonnegative]
  have data (index : Fin count) := coarse.2.1 time timeInside index
  have rawLower (index : Fin count) : changed.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference motion time index := by
    have actual := (le_div_iff₀ (sq_pos_of_pos (changed.length_pos (index.val + 1)))).mp (data index).2.2.1
    linarith only [actual]
  have rawUpper (index : Fin count) : diagonalDifference motion time index ≤ 2 * changed.length (index.val + 1) ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos (changed.length_pos (index.val + 1)))).mp (data index).2.2.2.1
  have radialBound (index : Fin count) : |radialShape motion time index| ≤ 1 / 2 := by
    have identity : radialShape motion time index = unstableShape motion time index + stableShape motion time index := by
      dsimp only [unstableShape, stableShape]
      ring
    rw [identity]
    apply (abs_add _ _).trans
    linarith only [(data index).1, (data index).2.1, thresholdSmall]
  have asymmetryBound (index : Fin count) : ‖centroidAsymmetry motion time index‖ ≤ changed.length (index.val + 1) / 64 := by
    have actual := (data index).2.2.2.2.1
    have lengthPositive := changed.length_pos (index.val + 1)
    have lengthOne := changed.length_le_one frequencyPositive ratioPositive (index.val + 1)
    have lengthSquare : changed.length (index.val + 1) ^ 2 ≤ changed.length (index.val + 1) := by nlinarith only [lengthOne, lengthPositive]
    apply actual.trans
    calc
      _ ≤ constant * changed.hessian * changed.length (index.val + 1) ^ 2 * 2 * Real.exp (2 * constant) := by gcongr
      _ = (2 * constant * changed.hessian * Real.exp (2 * constant)) * changed.length (index.val + 1) ^ 2 := by ring
      _ ≤ (1 / 64) * changed.length (index.val + 1) ^ 2 := mul_le_mul_of_nonneg_right memoryBound (sq_nonneg _)
      _ ≤ changed.length (index.val + 1) / 64 := by linarith only [lengthSquare]
  have commonControl (index : Fin count) (patch : Fin 4) : BoundaryCloseToCircle changed motion time index patch 1 := by
    have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
    have omegaOne : 1 ≤ changed.omega (index.val + 1) :=
      frequencyBound.trans (changed.omega_ge_frequency frequencyPositive (by dsimp only [changed]; linarith) _)
    have omegaConstant : constant ≤ changed.omega (index.val + 1) :=
      constantBound.trans (changed.omega_ge_frequency frequencyPositive (by dsimp only [changed]; linarith) _)
    have scalar : constant * (changed.omega (index.val + 1))⁻¹ ^ 2 ≤ 1 := by
      rw [inv_pow, ← div_eq_mul_inv]
      apply (div_le_iff₀ (pow_pos omegaPositive 2)).mpr
      nlinarith only [omegaOne, omegaConstant]
    obtain ⟨relabeling, periodic, relabelingBound, errorBound⟩ := (data index).2.2.2.2.2 patch
    exact ⟨relabeling, periodic, relabelingBound, errorBound.mono scalar⟩
  apply reference_boundary_label_gap_of_shape_geometry changed motion time
    (fun index => changed.radius_pos amplitudePositive frequencyPositive ratioPositive _) rawLower rawUpper radialBound asymmetryBound
    (fun index other distinct => (coarse.2.2 time timeInside index other distinct).1)
    (fun index => by simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using (lengths (index.val + 1)).le)
    (fun index => by simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using (radii (index.val + 1)).le)
    commonControl receiver source first second different

end EulerNonuniqueness.Paper
