import EulerNonuniqueness.Section6.PaperOddForcingNormSplit
import EulerNonuniqueness.Section6.PaperRelativeShapeForcingSplit

noncomputable section

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem quadrupoleTotalOddForcing_eq_centered_parts {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) :
    fourPointTotalOddForcing (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
        (fun patch => patchCentroid motion time index patch) (quadrupoleCentroidForcing scales motion time index) =
      fourPointOddInternalError (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
          (fun patch => patchCentroid motion time index patch) +
        fourPointOddPart (quadrupoleCenteredExternalIncrement scales motion index time) +
        fourPointOddPart (quadrupoleDilationPatchError scales motion index time) := by
  have identity : fourPointOddPart (quadrupoleCentroidForcing scales motion time index) =
      fourPointOddPart (quadrupoleCenteredExternalIncrement scales motion index time) +
        fourPointOddPart (quadrupoleDilationPatchError scales motion index time) := by
    ext <;> simp only [fourPointOddPart, quadrupoleCentroidForcing, quadrupoleCenteredExternalIncrement,
      quadrupoleDilationPatchError, Prod.fst_add, Prod.snd_add] <;> ring
  rw [fourPointTotalOddForcing, identity]
  abel

theorem quadrupoleTotalOddForcing_relative_norm_split {count : ℕ} (scales : Scales)
    (first second : PatchMotion count) (time : ℝ) (index : Fin count) :
    ‖fourPointTotalOddForcing (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
        (fun patch => patchCentroid first time index patch) (quadrupoleCentroidForcing scales first time index) -
      fourPointTotalOddForcing (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
        (fun patch => patchCentroid second time index patch) (quadrupoleCentroidForcing scales second time index)‖ ≤
      ‖fourPointOddInternalError (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
          (fun patch => patchCentroid first time index patch) -
        fourPointOddInternalError (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
          (fun patch => patchCentroid second time index patch)‖ +
        ‖quadrupoleCenteredExternalIncrement scales first index time - quadrupoleCenteredExternalIncrement scales second index time‖ +
        ‖quadrupoleDilationPatchError scales first index time - quadrupoleDilationPatchError scales second index time‖ := by
  rw [quadrupoleTotalOddForcing_eq_centered_parts, quadrupoleTotalOddForcing_eq_centered_parts,
    add_sub_add_comm, add_sub_add_comm, ← fourPointOddPart_sub, ← fourPointOddPart_sub]
  apply (norm_add_le _ _).trans
  have triangle := norm_add_le
    (fourPointOddInternalError (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
        (fun patch => patchCentroid first time index patch) -
      fourPointOddInternalError (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
        (fun patch => patchCentroid second time index patch))
    (fourPointOddPart (quadrupoleCenteredExternalIncrement scales first index time - quadrupoleCenteredExternalIncrement scales second index time))
  have centeredBound := fourPointOddPart_norm_le
    (quadrupoleCenteredExternalIncrement scales first index time - quadrupoleCenteredExternalIncrement scales second index time)
  have patchBound := fourPointOddPart_norm_le
    (quadrupoleDilationPatchError scales first index time - quadrupoleDilationPatchError scales second index time)
  linarith

end EulerNonuniqueness.Paper
