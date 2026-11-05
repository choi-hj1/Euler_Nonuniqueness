import EulerNonuniqueness.Section5.CascadeSourceShapeRadius
import EulerNonuniqueness.Section5.CascadeSourceCapMonotonicity

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem exists_actual_source_stopped_shape_radius_monotone
    {sourceRadius : ℝ} (sourcePositive : 0 < sourceRadius) :
    ∃ rawCap > 0,
    ∀ {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {requestedCap threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
      (prepared : CascadeSourcePreparedPair requestedCap scales orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    requestedCap ≤ rawCap →
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ time ∈ Icc 0 path.stop, ∀ label : Fin (count * 4),
      ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
      ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label) := by
  obtain ⟨rawCap, rawPositive, shapes⟩ := exists_actual_source_stopped_shape_radius sourcePositive
  refine ⟨rawCap, rawPositive, ?_⟩
  intro scales orbit sectionTime phase dipoleAngle requestedCap threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant
    count prepared ordered path time inside label
  exact shapes (prepared.enlargeCap ordered) path time inside label

end EulerNonuniqueness.Paper
