import EulerNonuniqueness.Section6.SourcePacketPhysicalComparison

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem exists_source_packet_paired_signed_comparison :
    ∃ constant ≥ (0 : ℝ), ∃ radius > (0 : ℝ),
    ∀ {count : ℕ} {reference alternative : FiniteMovingPatchFamily (count * 4)}
      {scales : Scales} {source : Fin count} {start horizon decay : ℝ},
    ∀ referenceGeometry : SourcePacketPhysicalGeometry reference scales source start horizon radius,
    ∀ alternativeGeometry : SourcePacketPhysicalGeometry alternative scales source start horizon radius,
    0 ≤ horizon →
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * referenceGeometry.physicalCost constant elapsed) volume 0 horizon →
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * alternativeGeometry.physicalCost constant elapsed) volume 0 horizon →
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * referenceGeometry.modelInput elapsed) volume 0 horizon →
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * alternativeGeometry.modelInput elapsed) volume 0 horizon →
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) *
      (alternativeGeometry.actualInput elapsed - referenceGeometry.actualInput elapsed)) volume 0 horizon ∧
    |(∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
        (alternativeGeometry.actualInput elapsed - referenceGeometry.actualInput elapsed)) -
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
        (alternativeGeometry.modelInput elapsed - referenceGeometry.modelInput elapsed))| ≤
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * alternativeGeometry.physicalCost constant elapsed) +
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * referenceGeometry.physicalCost constant elapsed) := by
  obtain ⟨constant, nonnegative, radius, positive, comparison⟩ := exists_source_packet_signed_physical_comparison
  refine ⟨constant, nonnegative, radius, positive, ?_⟩
  intro count reference alternative scales source start horizon decay referenceGeometry alternativeGeometry
    horizonNonnegative referenceCost alternativeCost referenceModel alternativeModel
  obtain ⟨referenceActual, referenceBound⟩ := comparison referenceGeometry horizonNonnegative referenceCost referenceModel
  obtain ⟨alternativeActual, alternativeBound⟩ := comparison alternativeGeometry horizonNonnegative alternativeCost alternativeModel
  have actualDifference : IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) *
      (alternativeGeometry.actualInput elapsed - referenceGeometry.actualInput elapsed)) volume 0 horizon := by
    simpa only [mul_sub] using alternativeActual.sub referenceActual
  refine ⟨actualDifference, ?_⟩
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub alternativeActual referenceActual,
    intervalIntegral.integral_sub alternativeModel referenceModel]
  have rearrange (actualAlternative actualReference modelAlternative modelReference : ℝ) :
      (actualAlternative - actualReference) - (modelAlternative - modelReference) =
        (actualAlternative - modelAlternative) - (actualReference - modelReference) := by ring
  rw [rearrange]
  exact (abs_sub _ _).trans (add_le_add alternativeBound referenceBound)

end EulerNonuniqueness.Paper
