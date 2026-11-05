import EulerNonuniqueness.Section5.CascadeGapCappedSpectralParameters
import EulerNonuniqueness.Section6.SeparatingOrbitUniformGap
import EulerNonuniqueness.Section5.CascadeSourceShapeRadius

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem exists_uniform_orbit_gap_spectral_stopped_cascade_parameters
    {sourceRadius : ℝ} (sourcePositive : 0 < sourceRadius)
    {alpha ratio : ℝ} (alphaPositive : 0 < alpha) (alphaSmall : alpha < 1) (ratioLarge : 2 < ratio)
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    {sectionTime tolerance timingConstant : ℝ} (sectionTimePositive : 0 < sectionTime)
    (tolerancePositive : 0 < tolerance) (toleranceSmall : tolerance < 1 / 8)
    (timingPositive : 0 < timingConstant) :
    ∃ rawCap > (0 : ℝ), ∃ threshold > (0 : ℝ), threshold < 1 / 8 ∧
    ∃ shapeRadius > (0 : ℝ), ∃ factor > (0 : ℝ), factor ≤ 1 / 8 ∧
    (∀ time : ℝ, ∀ target source : Fin 4, source ≠ target →
      2 * factor ≤ ‖EulerNonuniqueness.Section6.centrallySymmetricFourPoint
          (orbit.positive time) (orbit.negative time) target -
        EulerNonuniqueness.Section6.centrallySymmetricFourPoint
          (orbit.positive time) (orbit.negative time) source‖) ∧
    ∃ monitor > (0 : ℝ), ∃ boundaryConstant ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ scaleRoot : ℝ, rootMin ≤ scaleRoot → ∃ referenceConstant > (0 : ℝ), referenceConstant ≤ scaleRoot ^ 3 ∧
    ∀ᶠ frequency : ℝ in atTop,
      CascadeParameterPrerequisites ⟨alpha, scaleRoot ^ 3, ratio, frequency⟩ orbit
        sectionTime threshold tolerance timingConstant ∧
      ∀ count : ℕ, 2 ≤ count → ∃ phase dipoleAngle : ℕ → ℝ,
        PrescribedCascadePhases ⟨alpha, scaleRoot ^ 3, ratio, frequency⟩ orbit sectionTime count phase dipoleAngle ∧
        ∃ prepared : CascadeSourcePreparedPair rawCap ⟨alpha, scaleRoot ^ 3, ratio, frequency⟩ orbit sectionTime phase dipoleAngle
          threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
        ∃ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
        ∀ time ∈ Icc 0 path.stop, ∀ label : Fin (count * 4),
          ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
          ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label) := by
  obtain ⟨gap, gapPositive, separated⟩ := normalized.2.2.1
  let factorCap := min (gap / 4) (1 / 8)
  have capPositive : 0 < factorCap := lt_min (by positivity) (by norm_num)
  have orbitSeparated (time : ℝ) (target source : Fin 4) (different : source ≠ target) :
      2 * factorCap ≤ ‖EulerNonuniqueness.Section6.centrallySymmetricFourPoint
        (orbit.positive time) (orbit.negative time) target -
        EulerNonuniqueness.Section6.centrallySymmetricFourPoint
          (orbit.positive time) (orbit.negative time) source‖ := by
    have properties := separated time
    have bound := EulerNonuniqueness.Section6.central_configuration_pair_gap properties.1
      properties.2.1 properties.2.2.1 properties.2.2.2 target source different.symm
    have small := min_le_left (gap / 4) (1 / 8)
    dsimp only [factorCap]
    linarith
  obtain ⟨rawCap, rawPositive, threshold, thresholdPositive, thresholdSmall, shapeRadius, shapePositive,
    factor, factorPositive, factorSmall, factorCapped, monitor, monitorPositive, boundaryConstant, boundaryOne,
    rootMin, rootEight, constructions⟩ :=
    exists_uniform_gap_capped_spectral_stopped_cascade_parameters factorCap capPositive sourcePositive
      alphaPositive alphaSmall ratioLarge orbit normalized sectionTimePositive tolerancePositive toleranceSmall timingPositive
  refine ⟨rawCap, rawPositive, threshold, thresholdPositive, thresholdSmall, shapeRadius, shapePositive,
    factor, factorPositive, factorSmall, ?_, monitor, monitorPositive, boundaryConstant, boundaryOne,
    rootMin, rootEight, constructions⟩
  intro time target source different
  exact (mul_le_mul_of_nonneg_left factorCapped (by norm_num : (0 : ℝ) ≤ 2)).trans
    (orbitSeparated time target source different)

end EulerNonuniqueness.Paper

