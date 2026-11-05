import EulerNonuniqueness.Section4.ReferencePairwiseSafety
import EulerNonuniqueness.Section4.UniversalReferenceMechanicalData
import EulerNonuniqueness.Section4.ReferenceMaterialWitness

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 4000000

theorem Scales.eventually_reference_material_pair_vector_drift (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {threshold constant : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (constantNonnegative : 0 ≤ constant) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase : Fin count → ℝ,
      ∀ witness : ReferenceMaterialCoarseWitness {scales with frequency := frequency} phase threshold constant,
      ∀ time ∈ Icc (0 : ℝ) 2, ∀ first second : Fin count, first ≠ second →
      ‖(quadrupoleCenter witness.trajectory.movingFamily.patchMotion time first -
          quadrupoleCenter witness.trajectory.movingFamily.patchMotion time second) -
        ((({scales with frequency := frequency} : Scales).location (first.val + 1) : ℂ) -
          (({scales with frequency := frequency} : Scales).location (second.val + 1) : ℂ))‖ ≤
        |scales.location (first.val + 1) - scales.location (second.val + 1)| / 8 := by
  have ratioOne : 1 < scales.ratio := by linarith
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive
      thresholdSmall constantNonnegative,
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 1000),
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio)
      (by norm_num : (0 : ℝ) < 1 / 2000),
    scales.eventually_omega_pow_length_lt ratioOne alphaPositive 0 (by norm_num : (0 : ℝ) < 1 / 64),
    scales.eventually_omega_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 1000000),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually
      (eventually_lt_nhds (by positivity : (0 : ℝ) < Real.pi / (15120 * 64)))]
      with frequency frequencyBound mechanical lengths radii tinyLengths omegaLengths strainSmall
  intro count phase witness time inside first second different
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have data (current : ℝ) (member : current ∈ Icc (0 : ℝ) 2) (index : Fin count) :=
    mechanical witness.trajectory.movingFamily.patchMotion witness.evolution witness.coarse current member index
  have lengthSmall (index : Fin count) : changed.length (index.val + 1) ≤ changed.location (index.val + 1) / 1000 := by
    simpa only [changed, div_eq_mul_inv, one_div, one_mul, mul_comm] using (lengths (index.val + 1)).le
  have radiusSmall (index : Fin count) : changed.radius (index.val + 1) * (1 + 1 / 16) ≤
      changed.length (index.val + 1) / 1000 := by
    have small : changed.radius (index.val + 1) ≤ changed.length (index.val + 1) / 2000 := by
      simpa only [changed, div_eq_mul_inv, one_div, one_mul, mul_comm] using (radii (index.val + 1)).le
    nlinarith [changed.radius_pos amplitudePositive frequencyPositive ratioPositive (index.val + 1)]
  have lengthTiny (index : Fin count) : changed.length (index.val + 1) ≤ 1 / 64 := by
    simpa only [changed, pow_zero, one_mul] using (tinyLengths (index.val + 1)).le
  have omegaLength (index : Fin count) : changed.omega (index.val + 1) * changed.length (index.val + 1) ≤
      (1 / 1000000 : ℝ) * changed.location (index.val + 1) := by
    simpa only [changed] using (omegaLengths (index.val + 1)).le
  have globalInside (current : ℝ) (member : current ∈ Icc (0 : ℝ) 2) : current ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [member.1], by linarith [member.2]⟩
  have control (current : ℝ) (member : current ∈ Icc (0 : ℝ) 2) (index : Fin count) (patch : Fin 4) :
      BoundaryCloseToCircle changed witness.trajectory.movingFamily.patchMotion current index patch (1 / 16) := by
    obtain ⟨_, _, _, _, _, _, _, _, small, actual⟩ := data current member index
    obtain ⟨relabeling, periodic, relabelingBound, error⟩ := actual patch
    exact ⟨relabeling, periodic, relabelingBound, error.mono small⟩
  have radialSmall (current : ℝ) (member : current ∈ Icc (0 : ℝ) 2) (index : Fin count) :
      |radialShape witness.trajectory.movingFamily.patchMotion current index| ≤ 1 / 2 := by
    have identity : radialShape witness.trajectory.movingFamily.patchMotion current index =
        unstableShape witness.trajectory.movingFamily.patchMotion current index +
          stableShape witness.trajectory.movingFamily.patchMotion current index := by
      unfold unstableShape stableShape
      ring
    rw [identity]
    have actual := abs_add (unstableShape witness.trajectory.movingFamily.patchMotion current index)
      (stableShape witness.trajectory.movingFamily.patchMotion current index)
    linarith [(data current member index).2.2.2.2.1, (data current member index).2.2.2.2.2.1]
  have asymmetrySmall (current : ℝ) (member : current ∈ Icc (0 : ℝ) 2) (index : Fin count) :
      ‖centroidAsymmetry witness.trajectory.movingFamily.patchMotion current index‖ ≤ changed.length (index.val + 1) / 64 := by
    have actual := (data current member index).2.2.2.1
    have positive := changed.length_pos (index.val + 1)
    nlinarith [lengthTiny index]
  have drift := witness.trajectory.movingFamily.reference_pair_center_change_bound changed witness.densityIdentity
    witness.evolution (by norm_num : (0 : ℝ) ≤ 2) (fun _ member => member)
    amplitudePositive frequencyBound ratioBound alphaPositive witness.initial
    (fun current member _ => globalInside current member)
    (fun current member label angle => witness.trajectory.movingFamily_material_equation_of_margin
      witness.marginPositive (globalInside current member) (witness.safe current member) label angle)
    (fun current member index => (data current member index).2.1)
    (fun current member index => (data current member index).2.2.1)
    radialSmall asymmetrySmall
    (fun current member receiver source different => (witness.coarse.2.2 current member receiver source different).1)
    (fun current member receiver source different => (witness.coarse.2.2 current member receiver source different).2)
    lengthSmall control (by norm_num : (0 : ℝ) ≤ 1 / 16) le_rfl radiusSmall
    (by norm_num : (0 : ℝ) ≤ 1 / 1000000) omegaLength time inside first second different
  have rateSmall : (15120 / Real.pi) * changed.strain + 1800 * (1 / 1000000 : ℝ) ≤ 1 / 16 := by
    have scaled := mul_le_mul_of_nonneg_left strainSmall.le (by positivity : (0 : ℝ) ≤ 15120 / Real.pi)
    have coefficient : (15120 / Real.pi) * (Real.pi / (15120 * 64)) = (1 / 64 : ℝ) := by
      field_simp <;> ring
    rw [coefficient] at scaled
    linarith
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have weightedTime := mul_le_mul_of_nonneg_left inside.2
    (show 0 ≤ (15120 / Real.pi) * changed.strain + 1800 * (1 / 1000000 : ℝ) by positivity)
  have timeRate : ((15120 / Real.pi) * changed.strain + 1800 * (1 / 1000000 : ℝ)) * time ≤ 1 / 8 := by
    linarith
  exact drift.trans (by
    convert mul_le_mul_of_nonneg_right timeRate
      (abs_nonneg (changed.location (first.val + 1) - changed.location (second.val + 1))) using 1 <;>
      simp only [Scales.location] <;> ring)

end EulerNonuniqueness.Paper
