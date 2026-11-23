/-
Copyright (c) 2026 David A. Dalrymple. All rights reserved.
Released under MIT OR Apache-2.0 license as described in the file LICENSE.
Authors: dhai (davidad's Humanis AIs)
-/
module

import Wasserstein
import Lean.Util.CollectAxioms

/-! # Axiom audit

Generate the list from the imported environment: all public declarations whose defining
module is in the `Wasserstein` library, including generated projections and instances.
Fail if the generated list is unexpectedly empty or any declaration uses another axiom.
-/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx =>
      let modName := env.header.moduleNames[idx.toNat]!
      if (`Wasserstein).isPrefixOf modName && !isPrivateName name then some name else none
    | none => none
  let names := names.toArray.qsort Name.lt
  if names.size < 20 then
    throwError "Expected at least 20 public library declarations, found {names.size}"
  for name in names do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} depends on unexpected axiom {ax}"
    logInfo m!"{name}: {axioms.toList}"
  logInfo m!"Audited {names.size} public declarations."
