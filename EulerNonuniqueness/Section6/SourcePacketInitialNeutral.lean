import EulerNonuniqueness.Section5.CascadeInternallyStoppedPath
import EulerNonuniqueness.Section5.CascadeNonterminalInitialMoments
import EulerNonuniqueness.Section5.CascadeInitialSeparation

noncomputable section

namespace EulerNonuniqueness.Paper.CascadeInternallyStoppedPath

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
  {prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
    scaleRoot shapeRadius factor monitor boundaryConstant count}

theorem source_packet_initial_neutral (path : CascadeInternallyStoppedPath prepared)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (thresholdSmall : threshold ≤ 1 / 2) (index : Fin count) :
    centroidAsymmetry prepared.trajectory.movingFamily.patchMotion 0 index = 0 := by
  rcases lt_or_eq_of_le (Nat.succ_le_of_lt index.isLt) with nonterminal | terminal
  · exact (prepared.nonterminal_initial_invariants amplitudePositive frequencyPositive ratioPositive thresholdSmall
      index nonterminal).1
  · have centroids := path.evolution.cascade_terminal_initial_centroid path.stopPositive.le amplitudePositive
      frequencyPositive ratioPositive prepared.commonInitial index terminal
    unfold centroidAsymmetry
    rw [centroids 0, centroids 1, centroids 2, centroids 3]
    simp only [separatingInitialCenter,
      show (1 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 0 by decide,
      show (2 : Fin 4) ≠ 1 by decide, show (3 : Fin 4) ≠ 0 by decide,
      show (3 : Fin 4) ≠ 1 by decide, show (3 : Fin 4) ≠ 2 by decide, ↓reduceIte]
    ring

theorem source_packet_initial_first_moment (path : CascadeInternallyStoppedPath prepared)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (thresholdSmall : threshold ≤ 1 / 2) (index : Fin count) (center : ℂ) :
    (∫ position, quadrupoleDensity scales prepared.trajectory.movingFamily.patchMotion 0 index position •
      (position - center)) = 0 := by
  rw [path.evolution.integral_quadrupoleDensity_first_moment ⟨le_rfl, path.stopPositive.le⟩
    amplitudePositive frequencyPositive ratioPositive index center,
    path.source_packet_initial_neutral amplitudePositive frequencyPositive ratioPositive thresholdSmall index,
    smul_zero]

end EulerNonuniqueness.Paper.CascadeInternallyStoppedPath
