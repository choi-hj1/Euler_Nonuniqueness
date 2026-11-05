import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

/-!
# A diagonal subsequence of nested extractions

The diagonal of repeatedly extracted increasing sequences eventually satisfies
every eventual property of each fixed extraction. No topology is required.
-/

open Filter Function

namespace Nat

def nestedExtraction (extractions : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => id
  | stage + 1 => nestedExtraction extractions stage ∘ extractions stage

theorem strictMono_nestedExtraction {extractions : ℕ → ℕ → ℕ}
    (increasing : ∀ stage, StrictMono (extractions stage)) (stage : ℕ) :
    StrictMono (nestedExtraction extractions stage) := by
  induction stage with
  | zero => exact strictMono_id
  | succ stage induction => exact induction.comp (increasing stage)

theorem nestedExtraction_factor {extractions : ℕ → ℕ → ℕ}
    (increasing : ∀ stage, StrictMono (extractions stage)) {earlier later : ℕ}
    (ordered : earlier ≤ later) :
    ∃ tail : ℕ → ℕ, StrictMono tail ∧
      nestedExtraction extractions later = nestedExtraction extractions earlier ∘ tail := by
  induction ordered with
  | refl => exact ⟨id, strictMono_id, rfl⟩
  | @step later ordered induction =>
    obtain ⟨tail, tailIncreasing, factorization⟩ := induction
    refine ⟨tail ∘ extractions later, tailIncreasing.comp (increasing later), ?_⟩
    simp only [nestedExtraction, factorization, Function.comp_assoc]

theorem strictMono_nestedExtraction_diagonal {extractions : ℕ → ℕ → ℕ}
    (increasing : ∀ stage, StrictMono (extractions stage)) :
    StrictMono (fun index => nestedExtraction extractions index index) := by
  apply strictMono_nat_of_lt_succ
  intro index
  exact strictMono_nestedExtraction increasing index
    (lt_of_lt_of_le (Nat.lt_succ_self index) ((increasing index).id_le (index + 1)))

theorem eventually_nestedExtraction_diagonal {extractions : ℕ → ℕ → ℕ}
    (increasing : ∀ stage, StrictMono (extractions stage)) (stage : ℕ)
    {property : ℕ → Prop}
    (eventual : ∀ᶠ index in atTop, property (nestedExtraction extractions stage index)) :
    ∀ᶠ index in atTop, property (nestedExtraction extractions index index) := by
  obtain ⟨cutoff, afterCutoff⟩ := eventually_atTop.mp eventual
  filter_upwards [eventually_ge_atTop (max stage cutoff)] with index large
  obtain ⟨tail, tailIncreasing, factorization⟩ :=
    nestedExtraction_factor increasing (le_trans (le_max_left _ _) large)
  rw [factorization]
  exact afterCutoff (tail index)
    (le_trans (le_trans (le_max_right _ _) large) (tailIncreasing.id_le index))

end Nat
