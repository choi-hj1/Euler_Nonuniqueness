import EulerNonuniqueness.General.HomologicalJetCoordinates

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem coordinateQuadraticJet_spectral_transverse
    (projection generator originalGenerator : Space →L[ℝ] Space)
    (coordinates : Space ≃L[ℝ] Space) (differential originalSecond : BilinearEnd Space)
    (factors : ∀ direction, differential (projection direction) = differential direction)
    (fixes : ∀ direction, coordinates (projection direction) = projection direction)
    (annihilates : ∀ direction, projection (generator direction) = 0)
    (intertwines : ∀ direction, originalGenerator (coordinates direction) = coordinates (generator direction))
    (symmetric : ∀ first second, originalSecond first second = originalSecond second first)
    (differentiatedIntertwining : ∀ neutral direction,
      originalSecond (projection neutral) (coordinates direction) +
        originalGenerator (differential neutral direction) = differential neutral (generator direction))
    (direction correction : Space) (transverse : projection direction = 0) :
    coordinateQuadraticJet coordinates
        (differential + differential.flip.comp (ContinuousLinearMap.id ℝ Space - projection))
        originalGenerator originalSecond direction correction =
      coordinates.symm (originalSecond (coordinates direction)
        (coordinates (correction - projection correction))) := by
  have kernelZero (value : Space) (kernel : projection value = 0) : differential value = 0 := by
    rw [← factors value, kernel, map_zero]
  have directionZero := kernelZero direction transverse
  have generatorZero (value : Space) : differential (generator value) = 0 :=
    kernelZero _ (annihilates value)
  have inverseGenerator (value : Space) :
      coordinates.symm (originalGenerator (coordinates value)) = generator value := by
    rw [intertwines, coordinates.symm_apply_apply]
  have sourceSplit : originalSecond (coordinates direction) (coordinates correction) =
      originalSecond (coordinates direction) (coordinates (correction - projection correction)) +
        originalSecond (projection correction) (coordinates direction) := by
    rw [map_sub, fixes, map_sub, symmetric (projection correction) (coordinates direction)]
    abel
  have cancellation := differentiatedIntertwining correction direction
  unfold coordinateQuadraticJet
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    directionZero, ContinuousLinearMap.zero_apply, transverse, sub_zero, zero_add, inverseGenerator,
    generatorZero, add_zero]
  rw [sourceSplit]
  congr 1
  have identity := sub_eq_zero.mpr cancellation
  have shifted := congrArg (fun value : Space => value + originalSecond (coordinates direction)
    (coordinates (correction - projection correction))) identity
  abel_nf at shifted ⊢
  simpa only [zero_add] using shifted

end EulerNonuniqueness.General
