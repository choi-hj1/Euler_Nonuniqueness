import EulerNonuniqueness.General.CompactPrimitive

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

theorem IsCompact.exists_Icc_subset_Ioo {compactSet : Set ℝ} {lower upper : ℝ}
    (compact : IsCompact compactSet) (ordered : lower < upper)
    (contained : compactSet ⊆ Ioo lower upper) :
    ∃ innerLower innerUpper, compactSet ⊆ Ioo innerLower innerUpper ∧
      Icc innerLower innerUpper ⊆ Ioo lower upper := by
  by_cases nonempty : compactSet.Nonempty
  · obtain ⟨minimum, minimumMember, minimal⟩ := compact.exists_isMinOn nonempty continuousOn_id
    obtain ⟨maximum, maximumMember, maximal⟩ := compact.exists_isMaxOn nonempty continuousOn_id
    refine ⟨(lower + minimum) / 2, (maximum + upper) / 2, ?_, ?_⟩
    · intro point pointMember
      have minimumBound : minimum ≤ point := minimal pointMember
      have maximumBound : point ≤ maximum := maximal pointMember
      have first : lower < minimum := (contained minimumMember).1
      have second : maximum < upper := (contained maximumMember).2
      constructor <;> linarith
    · intro point pointMember
      have first : lower < minimum := (contained minimumMember).1
      have second : maximum < upper := (contained maximumMember).2
      constructor <;> linarith [pointMember.1, pointMember.2]
  · have empty : compactSet = ∅ := not_nonempty_iff_eq_empty.mp nonempty
    refine ⟨(lower + upper) / 2, (lower + upper) / 2, by simp [empty], ?_⟩
    intro point pointMember
    constructor <;> linarith [pointMember.1, pointMember.2]

theorem exists_contDiff_compact_primitive_supportedIn {function : ℝ → ℝ} {lower upper : ℝ}
    (smooth : ContDiff ℝ ∞ function) (compact : HasCompactSupport function)
    (ordered : lower < upper) (contained : tsupport function ⊆ Ioo lower upper)
    (zeroMean : (∫ point, function point) = 0) :
    ∃ primitive : ℝ → ℝ, ContDiff ℝ ∞ primitive ∧ HasCompactSupport primitive ∧
      tsupport primitive ⊆ Ioo lower upper ∧
      ∀ point, HasDerivAt primitive (function point) point := by
  obtain ⟨innerLower, innerUpper, inside, intervalInside⟩ :=
    compact.isCompact.exists_Icc_subset_Ioo ordered contained
  obtain ⟨primitive, primitiveSmooth, primitiveCompact, primitiveSupport, derivative⟩ :=
    exists_contDiff_compact_primitive_of_support_Ioo smooth
      ((subset_tsupport function).trans inside) zeroMean
  exact ⟨primitive, primitiveSmooth, primitiveCompact,
    primitiveSupport.trans intervalInside, derivative⟩
