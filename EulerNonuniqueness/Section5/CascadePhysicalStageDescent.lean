import EulerNonuniqueness.Section5.CascadePhysicalStageData

noncomputable section
open Set
namespace EulerNonuniqueness.Paper
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

variable {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
  {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant rawCap : ℝ}
  {count : ℕ}
  {prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle
    threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count}
  {path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair}
  {incomingTime extent magnitude coefficient error phaseTolerance timingTolerance matchingTolerance : ℝ}

theorem CascadePhysicalStageData.entry_lt_half {index : Fin count}
    (data : CascadePhysicalStageData prepared path index incomingTime extent magnitude coefficient error
      phaseTolerance timingTolerance matchingTolerance)
    (omegaPositive : 0 < scales.omega (index.val + 1))
    (predictedQuarter : scales.predictedTime sectionTime count (index.val + 1) < 1 / 4)
    (timingQuarter : timingTolerance / scales.omega (index.val + 1) < 1 / 4) :
    data.entry < 1 / 2 := by
  have upper := (le_abs_self (scales.omega (index.val + 1) *
    (data.entry - scales.predictedTime sectionTime count (index.val + 1)))).trans data.timing
  have difference : data.entry - scales.predictedTime sectionTime count (index.val + 1) ≤
      timingTolerance / scales.omega (index.val + 1) := by
    apply (le_div_iff₀ omegaPositive).mpr
    nlinarith only [upper]
  linarith only [difference, predictedQuarter, timingQuarter]

/-- Finite descent mechanics. The named producer remains an explicit obligation for actual stage factories. -/
theorem exists_physical_stage_family_of_next_stage_producer
    (countLarge : 2 ≤ count)
    (terminal : CascadePhysicalStageData prepared path ⟨count - 1, by omega⟩ incomingTime extent magnitude
      coefficient error phaseTolerance timingTolerance matchingTolerance)
    (omegaPositive : ∀ index : Fin count, 0 < scales.omega (index.val + 1))
    (predictedQuarter : ∀ index : Fin count, scales.predictedTime sectionTime count (index.val + 1) < 1 / 4)
    (timingQuarter : ∀ index : Fin count, timingTolerance / scales.omega (index.val + 1) < 1 / 4)
    (nextStageProducer : ∀ (index : Fin count) (nonterminal : index.val + 1 < count),
      ∀ prior : ∀ other : Fin count, index.val < other.val →
        CascadePhysicalStageData prepared path other incomingTime extent magnitude coefficient error
          phaseTolerance timingTolerance matchingTolerance,
      (∀ (first second : Fin count) (firstFiner : index.val < first.val) (secondFiner : index.val < second.val),
        first.val < second.val → (prior second secondFiner).entry < (prior first firstFiner).entry) →
      (prior ⟨index.val + 1, nonterminal⟩ (by simp)).entry ≤ 1 / 2 →
      ∃ data : CascadePhysicalStageData prepared path index incomingTime extent magnitude coefficient error
        phaseTolerance timingTolerance matchingTolerance,
        (prior ⟨index.val + 1, nonterminal⟩ (by simp)).entry < data.entry) :
    ∃ family : ∀ index : Fin count,
      CascadePhysicalStageData prepared path index incomingTime extent magnitude coefficient error
        phaseTolerance timingTolerance matchingTolerance,
      (∀ first second : Fin count, first.val < second.val → (family second).entry < (family first).entry) ∧
      ∀ index : Fin count, (family index).entry < 1 / 2 := by
  classical
  have buildTail : ∀ depth : ℕ, depth ≤ count - 1 →
      ∃ family : ∀ index : Fin count, count - 1 - depth ≤ index.val →
        CascadePhysicalStageData prepared path index incomingTime extent magnitude coefficient error
          phaseTolerance timingTolerance matchingTolerance,
        ∀ (first second : Fin count) (firstInside : count - 1 - depth ≤ first.val)
          (secondInside : count - 1 - depth ≤ second.val),
          first.val < second.val → (family second secondInside).entry < (family first firstInside).entry := by
    intro depth
    induction depth with
    | zero =>
      intro _
      let family : ∀ index : Fin count, count - 1 - 0 ≤ index.val →
          CascadePhysicalStageData prepared path index incomingTime extent magnitude coefficient error
            phaseTolerance timingTolerance matchingTolerance := by
        intro index inside
        have equal : index = (⟨count - 1, by omega⟩ : Fin count) := Fin.ext (by
          change index.val = count - 1
          omega)
        exact equal.symm ▸ terminal
      refine ⟨family, ?_⟩
      intro first second firstInside secondInside before
      omega
    | succ depth inductionHypothesis =>
      intro depthBound
      obtain ⟨old, oldOrder⟩ := inductionHypothesis (by omega)
      let index : Fin count := ⟨count - 1 - (depth + 1), by omega⟩
      have nonterminal : index.val + 1 < count := by dsimp only [index]; omega
      have previousCut : count - 1 - depth = index.val + 1 := by dsimp only [index]; omega
      let prior : ∀ other : Fin count, index.val < other.val →
          CascadePhysicalStageData prepared path other incomingTime extent magnitude coefficient error
            phaseTolerance timingTolerance matchingTolerance :=
        fun other finer => old other (by omega)
      have priorOrder (first second : Fin count) (firstFiner : index.val < first.val)
          (secondFiner : index.val < second.val) (before : first.val < second.val) :
          (prior second secondFiner).entry < (prior first firstFiner).entry :=
        oldOrder first second (by omega) (by omega) before
      have nearestHalf := (prior ⟨index.val + 1, nonterminal⟩ (by simp)).entry_lt_half
        (omegaPositive _) (predictedQuarter _) (timingQuarter _)
      obtain ⟨current, currentAfter⟩ := nextStageProducer index nonterminal prior priorOrder nearestHalf.le
      let family : ∀ other : Fin count, count - 1 - (depth + 1) ≤ other.val →
          CascadePhysicalStageData prepared path other incomingTime extent magnitude coefficient error
            phaseTolerance timingTolerance matchingTolerance :=
        fun other inside => if equal : other = index then equal.symm ▸ current else old other (by
          have different : other.val ≠ index.val := fun equalVal => equal (Fin.ext equalVal)
          dsimp only [index] at different
          omega)
      have familyCurrent : family index (by dsimp only [index]; omega) = current := by simp [family]
      have familyOld (other : Fin count) (inside : count - 1 - depth ≤ other.val) :
          family other (by omega) = old other inside := by
        have different : other ≠ index := by intro equal; subst other; omega
        simp [family, different]
      refine ⟨family, ?_⟩
      intro first second firstInside secondInside before
      have secondOld : count - 1 - depth ≤ second.val := by dsimp only [index] at previousCut; omega
      rw [familyOld second secondOld]
      by_cases firstCurrent : first = index
      · subst first
        rw [familyCurrent]
        have finer : index.val < second.val := before
        have secondPrior : (old second secondOld).entry = (prior second finer).entry := rfl
        rw [secondPrior]
        by_cases nearest : second = (⟨index.val + 1, nonterminal⟩ : Fin count)
        · subst second
          exact currentAfter
        · have afterNearest : index.val + 1 < second.val := by
            have different : second.val ≠ index.val + 1 := fun equal => nearest (Fin.ext equal)
            omega
          exact (priorOrder ⟨index.val + 1, nonterminal⟩ second (by simp) finer afterNearest).trans currentAfter
      · have firstOld : count - 1 - depth ≤ first.val := by
          have different : first.val ≠ index.val := fun equal => firstCurrent (Fin.ext equal)
          dsimp only [index] at different
          omega
        rw [familyOld first firstOld]
        exact oldOrder first second firstOld secondOld before
  obtain ⟨partialFamily, partialOrder⟩ := buildTail (count - 1) le_rfl
  let family := fun index : Fin count => partialFamily index (by omega)
  refine ⟨family, ?_, ?_⟩
  · intro first second before
    exact partialOrder first second (by omega) (by omega) before
  · intro index
    exact (family index).entry_lt_half (omegaPositive index) (predictedQuarter index) (timingQuarter index)

end EulerNonuniqueness.Paper
