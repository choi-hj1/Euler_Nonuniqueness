import EulerNonuniqueness.Section6.FinitePointDynamics

noncomputable section

namespace EulerNonuniqueness.Section6

abbrev FiniteQuadrupoleConfiguration (count : ℕ) := Fin count × Fin 4 → ℂ

def quadrupoleBlock {count : ℕ} (positions : FiniteQuadrupoleConfiguration count) (block : Fin count) :
    FourPointConfiguration := fun target => positions (block, target)

def quadrupoleBlockExternalField {count : ℕ} (coefficients : Fin count → ℝ)
    (positions : FiniteQuadrupoleConfiguration count) (block : Fin count) (location : ℂ) : ℂ :=
  Complex.I * ∑ sourceBlock ∈ Finset.univ.erase block, ∑ source : Fin 4,
    ((coefficients sourceBlock * fourPointSign source : ℝ) : ℂ) /
      star (location - positions (sourceBlock, source))

theorem finitePointField_quadrupole_block {count : ℕ} (coefficients : Fin count → ℝ)
    (positions : FiniteQuadrupoleConfiguration count) (block : Fin count) (target : Fin 4) :
    finitePointField (fun source : Fin count × Fin 4 => coefficients source.1 * fourPointSign source.2)
      positions (block, target) =
      fourPointField (coefficients block) (quadrupoleBlock positions block) target +
        quadrupoleBlockExternalField coefficients positions block (positions (block, target)) := by
  unfold finitePointField
  rw [Fintype.sum_prod_type]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ block), mul_add]
  congr 1
  · simpa only [finitePointField, quadrupoleBlock, Prod.mk.injEq, true_and] using
      congrFun (finitePointField_fourPoint_identity (coefficients block) (quadrupoleBlock positions block)) target
  · unfold quadrupoleBlockExternalField
    congr 1
    apply Finset.sum_congr rfl
    intro sourceBlock sourceInside
    have different : sourceBlock ≠ block := (Finset.mem_erase.mp sourceInside).1
    apply Finset.sum_congr rfl
    intro source _
    simp only [Prod.mk.injEq, different, false_and, if_false]

theorem coupledQuadrupole_block_hasDerivAt {count : ℕ}
    {coefficients : Fin count → ℝ} {trajectory : ℝ → FiniteQuadrupoleConfiguration count} {time : ℝ}
    (equation : HasDerivAt trajectory
      (finitePointField (fun source : Fin count × Fin 4 => coefficients source.1 * fourPointSign source.2)
        (trajectory time)) time) (block : Fin count) (target : Fin 4) :
    HasDerivAt (fun current => quadrupoleBlock (trajectory current) block target)
      (fourPointField (coefficients block) (quadrupoleBlock (trajectory time) block) target +
        quadrupoleBlockExternalField coefficients (trajectory time) block (trajectory time (block, target))) time := by
  have derivative := hasDerivAt_pi.mp equation (block, target)
  rw [finitePointField_quadrupole_block] at derivative
  exact derivative

theorem coupledQuadrupole_local_solution {count : ℕ} (coefficients : Fin count → ℝ)
    {positions : FiniteQuadrupoleConfiguration count} (noncollision : FinitePointNoncollision positions) :
    ∃ trajectory : ℝ → FiniteQuadrupoleConfiguration count, trajectory 0 = positions ∧
      ∃ radius > (0 : ℝ), ∀ time ∈ Set.Ioo (-radius) radius,
        FinitePointNoncollision (trajectory time) ∧
        ∀ block target, HasDerivAt (fun current => quadrupoleBlock (trajectory current) block target)
          (fourPointField (coefficients block) (quadrupoleBlock (trajectory time) block) target +
            quadrupoleBlockExternalField coefficients (trajectory time) block (trajectory time (block, target))) time := by
  obtain ⟨trajectory, initial, radius, radiusPositive, properties⟩ :=
    finitePointField_local_solution
      (fun source : Fin count × Fin 4 => coefficients source.1 * fourPointSign source.2) noncollision
  refine ⟨trajectory, initial, radius, radiusPositive, ?_⟩
  intro time member
  exact ⟨(properties time member).1, coupledQuadrupole_block_hasDerivAt (properties time member).2⟩

end EulerNonuniqueness.Section6
