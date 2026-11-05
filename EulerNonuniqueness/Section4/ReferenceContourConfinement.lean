import EulerNonuniqueness.Section4.ReferenceTrajectorySourceEnvelope
import EulerNonuniqueness.Section4.ReferenceLocalMaterialScaleBudget
import EulerNonuniqueness.Section3.MovingContourStrictSafetyConfinement

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_reference_contour_confinement :
    ∃ monitor > 0, ∃ forcingConstant ≥ (1 : ℝ), ∀ terminal : ℝ, 0 ≤ terminal →
    ∃ rootMin ≥ (8 : ℝ), ∀ (scales : Scales) (scaleRoot : ℝ),
    rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha → scales.strain ≤ 1 →
    ∀ {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
      {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
      {initial : MovingContourState (count * 4)}
      (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
        backwardHorizon forwardHorizon initial),
    (∀ index patch, configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) →
    (∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1)) →
    (∀ index, initial.2.2 index = standardCircleBanach) → initial.1 = 0 → 0 < margin →
    terminal < forwardHorizon →
    (∀ current ∈ Icc 0 terminal, margin ≤ infDist (trajectory.curve current)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) →
    (∀ current ∈ Ico 0 terminal, margin < infDist (trajectory.curve current)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) →
    (∀ current ∈ Icc 0 terminal, ∀ index,
      ReferenceCentroidFieldGeometry scales trajectory.movingFamily.patchMotion current index) →
    (∀ current ∈ Icc 0 terminal, ∀ index, ‖(trajectory.curve current).2.2 index - standardCircleBanach‖ < monitor) →
    (∀ current ∈ Icc 0 terminal, ∀ index, (trajectory.curve current).2.2 index ∈ contourContinuousVectorSubmodule) →
    ∀ current ∈ Icc 0 terminal, ∀ (index : Fin count) (patch : Fin 4),
      ‖diskPhysicalTransverseProjection (trajectory.spectralCoordinate (finProdFinEquiv (index, patch)) current)‖ <
        ((forcingConstant + 1) / (scaleRoot ^ 2 * scales.omega (index.val + 1) ^ 2)) / 8 := by
  obtain ⟨monitor, monitorPositive, confinement⟩ := exists_uniform_strict_safety_contour_confinement
  obtain ⟨constant, constantOne, scalesBound⟩ := Scales.exists_uniform_reference_local_material_scale_bound
  refine ⟨monitor, monitorPositive, constant, constantOne, ?_⟩
  intro terminal terminalNonnegative
  obtain ⟨minimum, minimumEight, confined⟩ := confinement constant terminal (by linarith) terminalNonnegative
  refine ⟨max minimum (192 * constant), le_trans minimumEight (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity frequencyLarge ratioLarge alphaPositive strainSmall
    count configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial trajectory
    densityIdentity radiusIdentity initialCircles initialClock marginPositive beforeFinal safe strictSafe geometry shapeSmall shapeMember
  have rootEight : 8 ≤ scaleRoot := minimumEight.trans ((le_max_left _ _).trans rootLarge)
  have rootPositive : 0 < scaleRoot := by linarith
  have frequencyPositive : 0 < scales.frequency := by linarith
  have ratioPositive : 0 < scales.ratio := by linarith
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  let naturalIndex := fun label : Fin (count * 4) => (finProdFinEquiv.symm label).1.val + 1
  let frequency := fun label => scales.omega (naturalIndex label)
  let distance := fun label => scales.length (naturalIndex label) / 400
  let weight := fun label => scales.referenceLocalExteriorWeight (naturalIndex label)
  let mass := fun label => 2 * scales.circulation (naturalIndex label)
  have scalar (label : Fin (count * 4)) := scalesBound scales scaleRoot amplitudeIdentity rootEight
    frequencyLarge ratioLarge strainSmall (naturalIndex label)
  have frequencyBound (label : Fin (count * 4)) : 1 ≤ frequency label :=
    frequencyLarge.trans (scales.omega_ge_frequency frequencyPositive (by linarith) _)
  have radius (label : Fin (count * 4)) : (trajectory.movingFamily.patch label).radius = scales.radius (naturalIndex label) := by
    simpa only [naturalIndex, Prod.mk.eta, Equiv.apply_symm_apply] using
      radiusIdentity (finProdFinEquiv.symm label).1 (finProdFinEquiv.symm label).2
  have sources (current : ℝ) (inside : current ∈ Icc 0 terminal) (label : Fin (count * 4)) :
      ∀ᶠ next in 𝓝 current,
        (∀ source ∈ Finset.univ.erase label, distance label + 3 * (trajectory.movingFamily.patch source).radius ≤
          ‖(trajectory.movingFamily.patch label).center next - (trajectory.movingFamily.patch source).center next‖) ∧
        (∫ position, inverseSquareVorticityWeight
          (trajectory.movingFamily.subfamilyVorticity (Finset.univ.erase label) next)
          ((trajectory.movingFamily.patch label).center next) position) ≤ weight label ∧
        (∫ position, |trajectory.movingFamily.patchVorticity next label position|) ≤ mass label := by
    simpa only [distance, weight, mass, naturalIndex, Prod.mk.eta, Equiv.apply_symm_apply] using
      trajectory.reference_eventually_source_envelopes scales densityIdentity radiusIdentity initialCircles
        marginPositive terminalNonnegative beforeFinal safe inside amplitudePositive frequencyLarge ratioLarge
        alphaPositive (finProdFinEquiv.symm label).1 (geometry current inside _) (finProdFinEquiv.symm label).2
  have allConfined := confined scaleRoot ((le_max_left _ _).trans rootLarge) trajectory initialCircles initialClock
    marginPositive frequency distance weight mass frequencyBound
  have densityMagnitude (label : Fin (count * 4)) : |configuration.density label| = scaleRoot ^ 3 * frequency label ^ 4 := by
    have identity := densityIdentity (finProdFinEquiv.symm label).1 (finProdFinEquiv.symm label).2
    simp only [Prod.mk.eta, Equiv.apply_symm_apply] at identity
    rw [identity, ← Real.norm_eq_abs, norm_mul, norm_mul, norm_patchSign, one_mul,
      Real.norm_of_nonneg amplitudePositive.le, Real.norm_of_nonneg (show 0 ≤ scales.omega (naturalIndex label) ^ 4 by positivity),
      amplitudeIdentity]
  have small (label : Fin (count * 4)) : 192 * (trajectory.movingFamily.patch label).radius ≤ distance label := by
    have rootBound : 192 * constant ≤ scaleRoot := (le_max_right _ _).trans rootLarge
    have denominator : 0 < scaleRoot * frequency label := mul_pos rootPositive (by linarith [frequencyBound label])
    have ratioBound := (scalar label).2.2.2.1
    have fraction : constant / (scaleRoot * frequency label) ≤ 1 / 192 := by
      apply (div_le_iff₀ denominator).2
      nlinarith [mul_le_mul_of_nonneg_left (frequencyBound label) rootPositive.le]
    have bound : scales.radius (naturalIndex label) / distance label ≤ 1 / 192 := ratioBound.trans fraction
    have positive : 0 < distance label := div_pos (scales.length_pos _) (by norm_num)
    rw [radius]
    have multiplied := (div_le_iff₀ positive).mp bound
    linarith
  have result := allConfined densityMagnitude (fun label => (scalar label).2.1)
    (fun label => by rw [radius]; exact (scalar label).2.2.2.1)
    (fun label => (scalar label).2.2.2.2.2) beforeFinal safe strictSafe
    (fun label => div_pos (scales.length_pos _) (by norm_num))
    (fun label => (scalar label).1) (fun label => (scalar label).2.2.2.2.1) small
    (fun current inside label => ((sources current inside label).self_of_nhds).1)
    (fun current inside label => ((sources current inside label).self_of_nhds).2.1)
    (fun current inside label => sources current ⟨inside.1, inside.2.le⟩ label) shapeSmall shapeMember
  intro current inside index patch
  simpa only [frequency, naturalIndex, Equiv.symm_apply_apply] using result current inside (finProdFinEquiv (index, patch))

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
