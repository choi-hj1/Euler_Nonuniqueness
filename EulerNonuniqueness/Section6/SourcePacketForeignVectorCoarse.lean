import EulerNonuniqueness.Section5.CascadeQuadrupoleForeignClearance
import EulerNonuniqueness.Section6.SourcePacketVectorProjectionBound
import EulerNonuniqueness.Section6.PaperRelativeLeadingStrainSum
import EulerNonuniqueness.Section6.PaperQuadrupoleStrainDerivative

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem FinitePatchEvolution.quadrupole_literal_strain_coarse_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time distance : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (source : Fin count) (location : ℂ)
    (distancePositive : 0 < distance)
    (separated : ∀ patch position, position ∈ motion.domain time source patch → distance ≤ ‖location - position‖) :
    ‖vorticityComplexStrain (quadrupoleDensity scales motion time source) location‖ ≤
      2 * scales.circulation (source.val + 1) / (Real.pi * distance ^ 2) := by
  rw [evolution.quadrupoleComplexStrain_sum inside source distancePositive separated]
  have patchBound (patch : Fin 4) :
      ‖(patchSign patch * scales.amplitude * scales.omega (source.val + 1) ^ 4) •
        ∫ position in motion.domain time source patch, biotSavartKernelStrain location position‖ ≤
      scales.circulation (source.val + 1) / (2 * Real.pi * distance ^ 2) := by
    have properties := evolution.2.2.2.1 time inside source patch
    have estimate := norm_integral_le_of_norm_le (μ := volume.restrict (motion.domain time source patch))
      (f := biotSavartKernelStrain location) (g := fun _ : ℂ => 1 / (2 * Real.pi * distance ^ 2))
      (integrableOn_const.mpr (Or.inr properties.2.1.measure_lt_top)) (by
        filter_upwards [ae_restrict_mem properties.1.measurableSet] with position member
        rw [norm_biotSavartKernelStrain]
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ distancePositive.le (separated patch position member) 2) (by positivity)))
    rw [integral_const] at estimate
    rw [norm_smul, Real.norm_eq_abs]
    apply (mul_le_mul_of_nonneg_left estimate (abs_nonneg _)).trans_eq
    simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
    have mass := evolution.patch_abs_density_mul_area inside amplitudePositive frequencyPositive ratioPositive source patch
    change _ * (volume _).toReal = _ at mass
    calc
      _ = (|patchSign patch * scales.amplitude * scales.omega (source.val + 1) ^ 4| *
          (volume (motion.domain time source patch)).toReal) / (2 * Real.pi * distance ^ 2) := by ring
      _ = _ := by rw [mass]
  have summed := (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum fun patch _ => patchBound patch)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at summed
  exact summed.trans_eq (by ring)

theorem Scales.exists_uniform_actual_foreign_source_vector_coarse_bound (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∃ radius > (0 : ℝ), ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ time ∈ Icc 0 path.stop, ∀ receiver source : Fin count,
      receiver ≠ source →
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.referenceWitness.trajectory.movingFamily.patchMotion
      let second := prepared.trajectory.movingFamily.patchMotion
      positiveHalfDiagonal first time receiver ≠ 0 → negativeHalfDiagonal first time receiver ≠ 0 →
      |(pointShapeChart (positiveHalfDiagonal first time receiver) (negativeHalfDiagonal first time receiver)).1| +
        |(pointShapeChart (positiveHalfDiagonal first time receiver) (negativeHalfDiagonal first time receiver)).2| ≤ radius →
      ‖relativeBlockSourceShapeInput changed second first receiver source time‖ ≤
        1280 * changed.circulation (source.val + 1) /
          (Real.pi * |changed.location (receiver.val + 1) - changed.location (source.val + 1)| ^ 2) := by
  obtain ⟨radius, radiusPositive, projection⟩ := exists_reference_strain_vector_projection_bound
  refine ⟨radius, radiusPositive, ?_⟩
  filter_upwards [scales.eventually_cascade_quadrupole_foreign_clearance amplitudePositive ratioBound alphaPositive
    orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    eventually_gt_atTop (0 : ℝ)] with frequency clearance frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver source different
  dsimp only
  intro positiveNonzero negativeNonzero shapeSmall
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let second := prepared.trajectory.movingFamily.patchMotion
  let gap := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
  have distinct : receiver.val + 1 ≠ source.val + 1 := fun equality => different (Fin.ext (Nat.add_right_cancel equality))
  have spacing := changed.location_sum_le_three_distance distinct
  have gapPositive : 0 < gap := by
    dsimp only [gap]
    linarith [changed.location_pos (receiver.val + 1), changed.location_pos (source.val + 1)]
  have member : source ∈ Finset.univ.erase receiver := Finset.mem_erase.mpr ⟨different.symm, Finset.mem_univ _⟩
  have gaps := clearance count phase dipoleAngle prepared path time inside receiver
  have firstInside : time ∈ Icc 0 2 := ⟨inside.1, by linarith [inside.2, path.stopBound]⟩
  have referenceBound := prepared.referenceWitness.evolution.quadrupole_literal_strain_coarse_bound firstInside
    amplitudePositive frequencyPositive (by dsimp only [changed]; linarith) source (quadrupoleCenter first time receiver)
    (show 0 < gap / 8 by positivity) (gaps.1 source member)
  have alternativeBound := path.evolution.quadrupole_literal_strain_coarse_bound inside
    amplitudePositive frequencyPositive (by dsimp only [changed]; linarith) source (quadrupoleCenter second time receiver)
    (show 0 < gap / 8 by positivity) (gaps.2 source member)
  have projected := projection (positiveHalfDiagonal first time receiver) (negativeHalfDiagonal first time receiver)
    (vorticityComplexStrain (quadrupoleDensity changed second time source) (quadrupoleCenter second time receiver) -
      vorticityComplexStrain (quadrupoleDensity changed first time source) (quadrupoleCenter first time receiver))
    positiveNonzero negativeNonzero shapeSmall
  change ‖relativeBlockSourceShapeInput changed second first receiver source time‖ ≤ _ at projected
  apply projected.trans
  have difference := norm_sub_le
    (vorticityComplexStrain (quadrupoleDensity changed second time source) (quadrupoleCenter second time receiver))
    (vorticityComplexStrain (quadrupoleDensity changed first time source) (quadrupoleCenter first time receiver))
  calc
    _ ≤ 5 * (2 * changed.circulation (source.val + 1) / (Real.pi * (gap / 8) ^ 2) +
        2 * changed.circulation (source.val + 1) / (Real.pi * (gap / 8) ^ 2)) :=
      mul_le_mul_of_nonneg_left (difference.trans (add_le_add alternativeBound referenceBound)) (by norm_num)
    _ = _ := by dsimp only [gap]; ring

end EulerNonuniqueness.Paper
