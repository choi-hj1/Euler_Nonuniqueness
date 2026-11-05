import EulerNonuniqueness.Section6.MovingQuadrupoleAngularMoment
import EulerNonuniqueness.Section6.MovingEulerExteriorWeightBound
import EulerNonuniqueness.Section6.MovingExternalPatchField
import EulerNonuniqueness.Section1.ForeignInteractionWeight

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

def foreignQuadrupolePatchLabels {count : ℕ} (index : Fin count) : Finset (Fin (count * 4)) :=
  ((Finset.univ.erase index).product (Finset.univ : Finset (Fin 4))).image finProdFinEquiv

theorem mem_foreignQuadrupolePatchLabels {count : ℕ} (receiver source : Fin count) (patch : Fin 4) :
    finProdFinEquiv (source, patch) ∈ foreignQuadrupolePatchLabels receiver ↔ source ≠ receiver := by
  constructor
  · intro member
    obtain ⟨pair, pairInside, equality⟩ := Finset.mem_image.mp member
    have pairEquality := finProdFinEquiv.injective equality
    subst pair
    exact (Finset.mem_erase.mp (Finset.mem_product.mp pairInside).1).1
  · intro different
    exact Finset.mem_image.mpr ⟨(source, patch), Finset.mem_product.mpr
      ⟨Finset.mem_erase.mpr ⟨different, Finset.mem_univ source⟩, Finset.mem_univ patch⟩, rfl⟩

theorem sum_foreignQuadrupolePatchLabels {count : ℕ} (receiver : Fin count) (function : Fin count → ℝ) :
    (∑ label ∈ foreignQuadrupolePatchLabels receiver, function (finProdFinEquiv.symm label).1) =
      4 * ∑ source ∈ Finset.univ.erase receiver, function source := by
  rw [foreignQuadrupolePatchLabels, Finset.sum_image
    (fun first _ second _ equality => finProdFinEquiv.injective equality)]
  simp only [Finset.product_eq_sprod]
  rw [Finset.sum_product]
  simp only [Equiv.symm_apply_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat]
  rw [Finset.mul_sum]

namespace FiniteMovingPatchFamily

theorem externalPatchVorticity_eq_subfamily {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (time : ℝ) (receiver : Fin count) :
    externalPatchVorticity scales family.patchMotion time receiver =
      family.subfamilyVorticity (foreignQuadrupolePatchLabels receiver) time := by
  funext position
  dsimp only [subfamilyVorticity, foreignQuadrupolePatchLabels]
  rw [Finset.sum_image (fun first _ second _ equality => finProdFinEquiv.injective equality)]
  simp only [Finset.product_eq_sprod]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro source member
  apply Finset.sum_congr rfl
  intro patch patchInside
  exact congrFun (family.patchDensity_eq scales densityEquation time source patch) position

theorem vorticity_eq_external_add_quadrupole {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (time : ℝ) (receiver : Fin count) :
    family.vorticity time = externalPatchVorticity scales family.patchMotion time receiver +
      quadrupoleDensity scales family.patchMotion time receiver := by
  rw [← family.patchVorticity_eq scales densityEquation]
  funext position
  exact (Finset.sum_erase_add (s := Finset.univ)
    (f := fun source : Fin count => quadrupoleDensity scales family.patchMotion time source position)
    (Finset.mem_univ receiver)).symm

theorem external_inverseSquare_weight_le_strain {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    (scales : Scales) {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (inside : time ∈ Icc 0 horizon)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) (receiver : Fin count) (center : ℂ)
    (separated : ∀ source ∈ Finset.univ.erase receiver, ∀ patch,
      ∀ position ∈ family.patchMotion.domain time source patch,
        |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 8 ≤ ‖center - position‖) :
    (∫ position, EulerNonuniqueness.Section6.inverseSquareVorticityWeight
      (externalPatchVorticity scales family.patchMotion time receiver) center position) ≤ 2304 * scales.strain := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  let distance := fun label : Fin (count * 4) =>
    |scales.location (receiver.val + 1) - scales.location ((finProdFinEquiv.symm label).1.val + 1)| / 8
  have labelDifferent (label : Fin (count * 4)) (member : label ∈ foreignQuadrupolePatchLabels receiver) :
      (finProdFinEquiv.symm label).1 ≠ receiver := by
    obtain ⟨⟨source, patch⟩, equality⟩ := finProdFinEquiv.surjective label
    subst label
    simpa only [Equiv.symm_apply_apply] using (mem_foreignQuadrupolePatchLabels receiver source patch).mp member
  have positive (label : Fin (count * 4)) (member : label ∈ foreignQuadrupolePatchLabels receiver) : 0 < distance label := by
    apply div_pos _ (by norm_num)
    apply scales.location_distance_pos
    intro equality
    exact labelDifferent label member (Fin.ext (Nat.add_right_cancel equality).symm)
  have individualSeparation (label : Fin (count * 4)) (member : label ∈ foreignQuadrupolePatchLabels receiver) :
      ∀ position ∈ (family.patch label).domain time, distance label ≤ ‖center - position‖ := by
    obtain ⟨⟨source, patch⟩, equality⟩ := finProdFinEquiv.surjective label
    subst label
    simpa only [distance, Equiv.symm_apply_apply, patchMotion] using separated source (Finset.mem_erase.mpr
      ⟨(mem_foreignQuadrupolePatchLabels receiver source patch).mp member, Finset.mem_univ source⟩) patch
  have actual := family.integral_inverseSquare_subfamily_le_circulations scales evolution inside densityEquation
    amplitudePositive frequencyPositive ratioPositive (foreignQuadrupolePatchLabels receiver) center distance positive individualSeparation
  rw [family.externalPatchVorticity_eq_subfamily scales densityEquation time receiver]
  apply actual.trans
  change (∑ label ∈ foreignQuadrupolePatchLabels receiver,
    (fun source : Fin count => scales.circulation (source.val + 1) /
      (|scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 8) ^ 2)
      (finProdFinEquiv.symm label).1) ≤ _
  rw [sum_foreignQuadrupolePatchLabels receiver (fun source : Fin count => scales.circulation (source.val + 1) /
      (|scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 8) ^ 2)]
  have finiteBound := mul_le_mul_of_nonneg_left
    (scales.sum_foreignInteractionWeight_le frequencyBound ratioBound alphaPositive receiver 2) (by norm_num : (0 : ℝ) ≤ 4)
  exact finiteBound.trans_eq (by unfold Scales.strain; norm_num; ring)

end FiniteMovingPatchFamily
end EulerNonuniqueness.Paper
