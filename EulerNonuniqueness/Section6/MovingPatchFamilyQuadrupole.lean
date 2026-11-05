import EulerNonuniqueness.Section6.MovingPatchFamilySourceComparison
import EulerNonuniqueness.General.ErasedProductSum

noncomputable section

namespace EulerNonuniqueness.Paper

namespace FiniteMovingPatchFamily

def quadrupoleSubfamily {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    (block : Fin count) : FiniteMovingPatchFamily 4 where
  patch := fun patch => family.patch (finProdFinEquiv (block, patch))
  density := fun patch => family.density (finProdFinEquiv (block, patch))

theorem exteriorTaylorCoefficient_eq_own_and_foreign_quadrupoles {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (receiver : Fin count × Fin 4)
    (center : ℝ → ℂ) (radius : ℝ) (power : ℕ) (time : ℝ) :
    family.exteriorTaylorCoefficient (Finset.univ.erase (finProdFinEquiv receiver)) center radius (power + 1) time =
      (family.quadrupoleSubfamily receiver.1).exteriorTaylorCoefficient (Finset.univ.erase receiver.2) center radius (power + 1) time +
        ∑ source ∈ Finset.univ.erase receiver.1,
          (family.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ center radius (power + 1) time := by
  simp_rw [family.exteriorTaylorCoefficient_eq_sum_sourceTaylorCoefficient]
  simp_rw [FiniteMovingPatchFamily.exteriorTaylorCoefficient_eq_sum_sourceTaylorCoefficient]
  exact EulerNonuniqueness.General.sum_erase_equiv_prod finProdFinEquiv
    (fun label => (family.patch label).sourceTaylorCoefficient (family.density label) (center time) radius power time)
    receiver.1 receiver.2

end FiniteMovingPatchFamily

namespace MovingPatchFamilySourceComparison

def quadrupole {count : ℕ} (comparison : MovingPatchFamilySourceComparison (count * 4))
    (block : Fin count) : MovingPatchFamilySourceComparison 4 where
  first := comparison.first.quadrupoleSubfamily block
  second := comparison.second.quadrupoleSubfamily block
  densityEqual := fun patch => comparison.densityEqual (finProdFinEquiv (block, patch))
  firstReceiver := comparison.firstReceiver
  secondReceiver := comparison.secondReceiver
  receiverRadius := comparison.receiverRadius
  receiverRadius_nonnegative := comparison.receiverRadius_nonnegative
  time := comparison.time
  initial := fun patch => comparison.initial (finProdFinEquiv (block, patch))
  final := fun patch => comparison.final (finProdFinEquiv (block, patch))
  firstShape := fun patch => comparison.firstShape (finProdFinEquiv (block, patch))
  secondShape := fun patch => comparison.secondShape (finProdFinEquiv (block, patch))
  radiusEqual := fun patch => comparison.radiusEqual (finProdFinEquiv (block, patch))
  phaseEqual := fun patch => comparison.phaseEqual (finProdFinEquiv (block, patch))
  firstArea := fun patch => comparison.firstArea (finProdFinEquiv (block, patch))
  secondArea := fun patch => comparison.secondArea (finProdFinEquiv (block, patch))

theorem exteriorTaylorCoefficient_difference_eq_own_and_foreign_quadrupoles {count : ℕ}
    (comparison : MovingPatchFamilySourceComparison (count * 4)) (receiver : Fin count × Fin 4) (power : ℕ) :
    comparison.first.exteriorTaylorCoefficient (Finset.univ.erase (finProdFinEquiv receiver)) comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
      comparison.second.exteriorTaylorCoefficient (Finset.univ.erase (finProdFinEquiv receiver)) comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time =
    ((comparison.quadrupole receiver.1).first.exteriorTaylorCoefficient (Finset.univ.erase receiver.2) comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
      (comparison.quadrupole receiver.1).second.exteriorTaylorCoefficient (Finset.univ.erase receiver.2) comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time) +
      ∑ source ∈ Finset.univ.erase receiver.1,
        ((comparison.quadrupole source).first.exteriorTaylorCoefficient Finset.univ comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
          (comparison.quadrupole source).second.exteriorTaylorCoefficient Finset.univ comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time) := by
  rw [comparison.first.exteriorTaylorCoefficient_eq_own_and_foreign_quadrupoles,
    comparison.second.exteriorTaylorCoefficient_eq_own_and_foreign_quadrupoles]
  dsimp only [quadrupole]
  rw [Finset.sum_sub_distrib]
  abel

end MovingPatchFamilySourceComparison

end EulerNonuniqueness.Paper
