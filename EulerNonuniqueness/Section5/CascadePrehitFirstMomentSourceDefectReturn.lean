import EulerNonuniqueness.Section5.CascadePrehitNeutralReturn
import EulerNonuniqueness.Section5.CascadeFirstMomentSourceDefect

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_prehit_firstMoment_source_defect_return :
    ∃ memory ≥ (1 : ℝ), ∃ sourceRadius > (0 : ℝ), ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
      threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
      0 < factor → factor ≤ 1 / 8 →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ index : Fin count, index.val + 1 < count → ∀ (finish : ℝ), 0 ≤ finish → ∀ (finishBound : finish ≤ path.stop),
      (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
      ∀ (time : ℝ) (inside : time ∈ Icc 0 finish),
      ∃ shapes : ∀ patch : Fin 4, ∀ label,
        ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
        ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label),
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      let radius := factor / 39321600 * changed.location (index.val + 1)
      let comparison := fun patch => prepared.sourceComparison path
        (show time ∈ Icc 0 path.stop from ⟨inside.1, inside.2.trans finishBound⟩)
        (finProdFinEquiv (index, patch)) (shapes patch)
      let selected := foreignQuadrupolePatchLabels index
      let difference := ∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time radius power -
        quadrupoleExteriorCoefficient changed second index time radius power‖
      HasDerivAt (relativeNormalizedFirstMoment changed first second index)
        (relativeFirstMomentExternalVelocity changed first second index time) time ∧
      relativeNormalizedFirstMoment changed first second index time =
        (∫ current in (0 : ℝ)..time, relativeFirstMomentExternalVelocity changed first second index current) ∧
      relativeFirstMomentSourceDefect changed first second index time ≤ max 0 (
        (96 / Real.pi * (2304 * changed.strain)) *
          ((24 * changed.location (index.val + 1) / radius) *
            ‖quadrupoleNormalizedCentroidOffsets first index time (changed.length (index.val + 1)) -
              quadrupoleNormalizedCentroidOffsets second index time (changed.length (index.val + 1))‖) +
        (4 * memory * changed.hessian + 36 * changed.location (index.val + 1) / radius) * difference +
        (constant / (factor / 39321600)) *
          (changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2) *
          ∑ patch : Fin 4,
            ((96 / Real.pi * (2304 * changed.strain / (factor / 8) ^ 2)) *
              ((comparison patch).source (finProdFinEquiv (index, patch))).spectralDifferenceBudget +
            (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
              ‖(comparison patch).first.exteriorTaylorCoefficient selected (comparison patch).firstReceiver radius (power + 1) time -
                (comparison patch).second.exteriorTaylorCoefficient selected (comparison patch).secondReceiver radius (power + 1) time‖) *
              ‖diskPhysicalTransverseProjection ((comparison patch).final (finProdFinEquiv (index, patch)))‖)) := by
  obtain ⟨memory, memoryOne, sourceRadius, sourcePositive, rawCap, rawPositive, constant, constantNonnegative, actual⟩ :=
    exists_uniform_actual_prehit_firstMoment_return
  refine ⟨memory, memoryOne, sourceRadius, sourcePositive, rawCap, rawPositive, constant, constantNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor
    boundaryConstant thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  filter_upwards [actual scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative
    rootOne boundaryOne factorPositive factorSmall] with frequency bounds
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  obtain ⟨shapes, derivative, original, rate⟩ :=
    bounds count phase dipoleAngle prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  refine ⟨shapes, derivative, original, ?_⟩
  dsimp only at rate ⊢
  unfold relativeFirstMomentSourceDefect
  apply max_le_max_left
  apply (sub_le_iff_le_add).mpr
  exact rate.trans_eq (by ring)

end EulerNonuniqueness.Paper
