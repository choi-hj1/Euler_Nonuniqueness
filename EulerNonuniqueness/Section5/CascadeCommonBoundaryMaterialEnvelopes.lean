import EulerNonuniqueness.Section5.CascadeStoppedMaterialGeometry
import EulerNonuniqueness.Section5.CascadeGeometricScaleSmallness
import EulerNonuniqueness.Section5.CascadeMaterialScaleBudget
import EulerNonuniqueness.Section4.UniversalReferenceMechanicalData
import EulerNonuniqueness.Section4.ReferenceTrajectorySourceEnvelope

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

open EulerNonuniqueness.Section6

theorem exists_uniform_actual_common_boundary_material_envelopes
    (factor : ℝ) (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∃ rootMin ≥ (8 : ℝ), ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot →
    scales.amplitude = scaleRoot ^ 3 → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ threshold referenceConstant : ℝ, threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor boundaryConstant : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared,
      ∀ time ∈ Icc 0 path.stop, ∀ (index : Fin count) (patch : Fin 4),
      let changed : Scales := {scales with frequency := frequency}
      let label := finProdFinEquiv (index, patch)
      let first := prepared.referenceWitness.trajectory.movingFamily
      let final := prepared.trajectory.movingFamily
      let firstDistance := changed.length (index.val + 1) / 400
      let finalDistance := factor * changed.length (index.val + 1) / 400
      192 * (first.patch label).radius ≤ firstDistance ∧
      192 * (final.patch label).radius ≤ finalDistance ∧
      (∀ᶠ current in 𝓝 time,
        (∀ source ∈ Finset.univ.erase label, firstDistance + 3 * (first.patch source).radius ≤
          ‖(first.patch label).center current - (first.patch source).center current‖) ∧
        (∫ position, inverseSquareVorticityWeight (first.subfamilyVorticity (Finset.univ.erase label) current)
          ((first.patch label).center current) position) ≤ changed.referenceLocalExteriorWeight (index.val + 1) ∧
        (∫ position, |first.patchVorticity current label position|) ≤ 2 * changed.circulation (index.val + 1)) ∧
      (∀ᶠ current in 𝓝 time,
        (∀ source ∈ Finset.univ.erase label, finalDistance + 3 * (final.patch source).radius ≤
          ‖(final.patch label).center current - (final.patch source).center current‖) ∧
        (∫ position, inverseSquareVorticityWeight (final.subfamilyVorticity (Finset.univ.erase label) current)
          ((final.patch label).center current) position) ≤ changed.cascadeLocalExteriorWeight factor (index.val + 1) ∧
        (∫ position, |final.patchVorticity current label position|) ≤ 2 * changed.circulation (index.val + 1)) := by
  obtain ⟨firstConstant, firstOne, firstScales⟩ := Scales.exists_uniform_reference_local_material_scale_bound
  obtain ⟨finalConstant, finalOne, finalScales⟩ :=
    Scales.exists_uniform_cascade_local_material_scale_bound factor factorPositive factorSmall
  let rootMin := max 8 (max (192 * firstConstant) (192 * finalConstant))
  refine ⟨rootMin, le_max_left _ _, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive threshold referenceConstant thresholdSmall referenceNonnegative
  have rootEight : 8 ≤ scaleRoot := (le_max_left _ _).trans rootLarge
  have rootPositive : 0 < scaleRoot := by linarith
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  filter_upwards [scales.eventually_universal_reference_mechanical_data amplitudePositive ratioLarge alphaPositive thresholdSmall referenceNonnegative,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioLarge alphaPositive factorPositive factorSmall
      (bound := 3) (le_refl _), eventually_ge_atTop (1 : ℝ),
    (scales.strain_tendsto_zero ratioLarge alphaPositive).eventually (eventually_lt_nhds zero_lt_one)]
    with frequency mechanical geometry frequencyOne strainSmall
  intro count orbit sectionTime phase dipoleAngle shapeRadius monitor boundaryConstant prepared path time inside index patch
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith
  have omegaOne : 1 ≤ changed.omega (index.val + 1) :=
    frequencyOne.trans (changed.omega_ge_frequency frequencyPositive (by linarith) _)
  have referenceInside : time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, by linarith [inside.2, path.stopBound]⟩
  have firstGeometry := (mechanical prepared.referenceWitness.trajectory.movingFamily.patchMotion
    prepared.referenceWitness.evolution prepared.referenceWitness.coarse time referenceInside index).1
  have firstSources := prepared.referenceWitness.trajectory.reference_eventually_source_envelopes changed
    prepared.referenceWitness.densityIdentity prepared.referenceWitness.radiusIdentity (fun _ => rfl)
    prepared.referenceWitness.marginPositive (by norm_num) (by norm_num) prepared.referenceWitness.safe referenceInside
    amplitudePositive frequencyOne ratioLarge alphaPositive index firstGeometry patch
  have finalSources := prepared.trajectory.movingFamily.cascade_eventually_comoving_source_envelopes changed
    path.evolution inside prepared.densityIdentity prepared.radiusIdentity amplitudePositive frequencyOne ratioLarge alphaPositive
    factor factorPositive factorSmall (path.internalClosed time inside)
    (fun label => (path.externalMonitors time inside (.extent label)).le)
    (fun receiver source => (path.externalMonitors time inside (.lower receiver source)).le)
    (fun block => (geometry (block.val + 1)).2.2.1)
    (fun block => (geometry (block.val + 1)).2.1)
    (fun block => (geometry (block.val + 1)).2.2.2) index patch
  have firstScalar := firstScales changed scaleRoot amplitudeIdentity rootEight frequencyOne ratioLarge strainSmall.le (index.val + 1)
  have finalScalar := finalScales changed scaleRoot amplitudeIdentity rootEight frequencyOne ratioLarge strainSmall.le (index.val + 1)
  have firstScale : 192 * (prepared.referenceWitness.trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).radius ≤
      changed.length (index.val + 1) / 400 := by
    change 192 * prepared.referenceWitness.configuration.radius (finProdFinEquiv (index, patch)) ≤ _
    rw [prepared.referenceWitness.radiusIdentity index patch]
    have numerator : 192 * firstConstant ≤ scaleRoot := (le_max_left _ _).trans ((le_max_right _ _).trans rootLarge)
    have denominator : 0 < scaleRoot * changed.omega (index.val + 1) := by positivity
    have fraction : firstConstant / (scaleRoot * changed.omega (index.val + 1)) ≤ 1 / 192 := by
      apply (div_le_iff₀ denominator).mpr
      nlinarith [mul_le_mul_of_nonneg_left omegaOne rootPositive.le]
    have radiusBound := (firstScalar.2.2.2.1.trans fraction)
    have multiplied := (div_le_iff₀ (div_pos (changed.length_pos _) (by norm_num : (0 : ℝ) < 400))).mp radiusBound
    linarith
  have finalScale : 192 * (prepared.trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).radius ≤
      factor * changed.length (index.val + 1) / 400 := by
    change 192 * prepared.configuration.radius (finProdFinEquiv (index, patch)) ≤ _
    rw [prepared.radiusIdentity index patch]
    have numerator : 192 * finalConstant ≤ scaleRoot := (le_max_right _ _).trans ((le_max_right _ _).trans rootLarge)
    have denominator : 0 < scaleRoot * changed.omega (index.val + 1) := by positivity
    have fraction : finalConstant / (scaleRoot * changed.omega (index.val + 1)) ≤ 1 / 192 := by
      apply (div_le_iff₀ denominator).mpr
      nlinarith [mul_le_mul_of_nonneg_left omegaOne rootPositive.le]
    have radiusBound := finalScalar.2.2.2.1.trans fraction
    have multiplied := (div_le_iff₀ (div_pos (mul_pos factorPositive (changed.length_pos _)) (by norm_num : (0 : ℝ) < 400))).mp radiusBound
    linarith
  exact ⟨firstScale, finalScale, firstSources, finalSources⟩

end EulerNonuniqueness.Paper
