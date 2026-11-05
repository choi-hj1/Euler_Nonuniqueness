import EulerNonuniqueness.Section5.CascadeSourceStoppedParameters
import EulerNonuniqueness.Section5.CascadeSourceShapeRadius

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem exists_uniform_spectral_stopped_cascade_parameters
    {sourceRadius : ℝ} (sourcePositive : 0 < sourceRadius)
    {alpha ratio : ℝ} (alphaPositive : 0 < alpha) (alphaSmall : alpha < 1) (ratioLarge : 2 < ratio)
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    {sectionTime tolerance timingConstant : ℝ} (sectionTimePositive : 0 < sectionTime)
    (tolerancePositive : 0 < tolerance) (toleranceSmall : tolerance < 1 / 8)
    (timingPositive : 0 < timingConstant) :
    ∃ rawCap > (0 : ℝ), ∃ threshold > (0 : ℝ), threshold < 1 / 8 ∧
    ∃ shapeRadius > (0 : ℝ), ∃ factor > (0 : ℝ), factor ≤ 1 / 8 ∧
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
  obtain ⟨rawCap, rawPositive, shapes⟩ := exists_actual_source_stopped_shape_radius sourcePositive
  obtain ⟨threshold, thresholdPositive, thresholdSmall, shapeRadius, shapePositive,
    factor, factorPositive, factorSmall, monitor, monitorPositive, boundaryConstant, boundaryOne,
    rootMin, rootEight, constructions⟩ :=
    exists_uniform_source_stopped_cascade_parameters rawCap rawPositive alphaPositive alphaSmall ratioLarge
      orbit normalized sectionTimePositive tolerancePositive toleranceSmall timingPositive
  refine ⟨rawCap, rawPositive, threshold, thresholdPositive, thresholdSmall, shapeRadius, shapePositive,
    factor, factorPositive, factorSmall, monitor, monitorPositive, boundaryConstant, boundaryOne, rootMin, rootEight, ?_⟩
  intro scaleRoot rootLarge
  obtain ⟨referenceConstant, referencePositive, referenceAmplitudeBound, parameters⟩ := constructions scaleRoot rootLarge
  refine ⟨referenceConstant, referencePositive, referenceAmplitudeBound, ?_⟩
  filter_upwards [parameters] with frequency actual
  refine ⟨actual.1, ?_⟩
  intro count countLarge
  obtain ⟨phase, dipoleAngle, prescribed, prepared, ⟨path⟩⟩ := actual.2 count countLarge
  exact ⟨phase, dipoleAngle, prescribed, prepared, path, shapes prepared path⟩

end EulerNonuniqueness.Paper
