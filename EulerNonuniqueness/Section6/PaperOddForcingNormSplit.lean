import EulerNonuniqueness.Section6.PaperDilationForcingParts

noncomputable section

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem quadrupoleTotalOddForcing_norm_split {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) :
    ‖fourPointTotalOddForcing (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
        (fun patch => patchCentroid motion time index patch) (quadrupoleCentroidForcing scales motion time index)‖ ≤
      ‖fourPointOddInternalError (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
          (fun patch => patchCentroid motion time index patch)‖ +
        ‖quadrupoleCenteredExternalIncrement scales motion index time‖ +
        ‖quadrupoleDilationPatchError scales motion index time‖ := by
  let external : FourPointConfiguration := fun patch =>
    biotSavart (externalPatchVorticity scales motion time index) (patchCentroid motion time index patch)
  have identity : fourPointOddPart (quadrupoleCentroidForcing scales motion time index) =
      fourPointOddPart (quadrupoleCenteredExternalIncrement scales motion index time) +
        fourPointOddPart (quadrupoleDilationPatchError scales motion index time) := by
    ext <;> simp only [fourPointOddPart, quadrupoleCentroidForcing, quadrupoleCenteredExternalIncrement,
      quadrupoleDilationPatchError, Prod.fst_add, Prod.snd_add] <;> ring
  rw [fourPointTotalOddForcing, identity]
  apply (norm_add_le _ _).trans
  have triangle := norm_add_le (fourPointOddPart (quadrupoleCenteredExternalIncrement scales motion index time))
    (fourPointOddPart (quadrupoleDilationPatchError scales motion index time))
  have first := fourPointOddPart_norm_le (quadrupoleCenteredExternalIncrement scales motion index time)
  have second := fourPointOddPart_norm_le (quadrupoleDilationPatchError scales motion index time)
  linarith

end EulerNonuniqueness.Paper
