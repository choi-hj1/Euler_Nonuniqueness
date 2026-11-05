import Comparator
import EulerNonuniqueness
import Lean.Util.FoldConsts

/-!
# Transitive proof dependency audit

Every theorem defined in the project library or comparator is checked.
The traversal includes statement types, theorem proofs, and opaque bodies.
This audit checks dependency safety; `FullVerification.lean` separately checks the closed target proof.
-/

open Lean Elab Command

set_option maxHeartbeats 0 in
run_cmd do
  let environment ← getEnv
  let roots := environment.constants.fold (init := #[]) fun roots name information =>
    match information with
    | .thmInfo _ =>
      match environment.getModuleIdxFor? name with
      | some index =>
        let moduleName := environment.header.moduleNames[index.toNat]!.toString
        if moduleName == "Comparator" || moduleName.startsWith "EulerNonuniqueness" then
          roots.push name
        else roots
      | none => roots
    | _ => roots
  unless roots.contains ``EulerNonuniqueness.main_conditional do
    throwError "The conditional assembly was not included in the dependency audit"
  unless roots.contains ``EulerNonuniqueness.lemma81 do
    throwError "The proved local compactness theorem was not included in the dependency audit"
  unless roots.contains ``EulerNonuniquenessComparator.target_iff do
    throwError "The independent target comparator was not included in the dependency audit"
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut inspected : NameSet := {}
  let mut pending := roots
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless inspected.contains name do
      inspected := inspected.insert name
      let some information := environment.find? name |
        throwError "Missing dependency declaration: {name}"
      if information.isUnsafe || information.isPartial then
        throwError "Unsafe or partial dependency declaration: {name}"
      if let .axiomInfo _ := information then
        unless permitted.contains name do
          throwError "Unapproved axiom declaration: {name}"
      pending := pending ++ information.type.getUsedConstants
      if let some body := information.value? (allowOpaque := true) then
        pending := pending ++ body.getUsedConstants
  logInfo m!"PROJECT_PROOF_ROOTS {roots.size}"
  logInfo m!"PROJECT_TRANSITIVE_SAFE {inspected.size}"
  logInfo "PROJECT_PROOF_DEPENDENCY_AUDIT_COMPLETE"
