import LeanPaper.AxiomWalk
import AuditFixtures

open Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LocalFixture
axiom forbiddenNat : Nat
noncomputable def pick : Nat := forbiddenNat
structure S9 where
  x : Fin (pick + 1)
end LocalFixture

run_cmd Elab.Command.liftCoreM do
  let env ← getEnv
  for root in #[`AuditFixtures.S9, `AuditFixtures.S9.mk,
      `AuditFixtures.M1, `AuditFixtures.M2, `AuditFixtures.M2.mk,
      `AuditFixtures.hidden] do
    let r := LeanPaper.AxiomWalk.collect env #[root]
    unless r.axioms.contains `AuditFixtures.forbiddenNat do
      throwError m!"REGRESSION_MISSING_IMPORTED_AXIOM {root}"
    unless r.missing.isEmpty do
      throwError m!"REGRESSION_UNEXPECTED_MISSING_CONSTANT {root}"
    match LeanPaper.AxiomWalk.check r [] with
    | .ok () => throwError m!"REGRESSION_FALSE_ACCEPTANCE {root}"
    | .error _ => pure ()
  let proofResult := LeanPaper.AxiomWalk.collect env #[`AuditFixtures.wrapped]
  unless proofResult.axioms.contains `AuditFixtures.forbiddenProof do
    throwError "REGRESSION_MISSING_PROOF_BODY_AXIOM"
  let privateResult := LeanPaper.AxiomWalk.collect env #[`AuditFixtures.throughPrivate]
  if privateResult.axioms.isEmpty then
    throwError "REGRESSION_MISSING_PRIVATE_AXIOM"
  unless privateResult.missing.isEmpty do
    throwError "REGRESSION_PRIVATE_BODY_UNAVAILABLE"
  let localResult := LeanPaper.AxiomWalk.collect env #[`LocalFixture.S9]
  unless localResult.axioms.contains `LocalFixture.forbiddenNat do
    throwError "REGRESSION_MISSING_LOCAL_AXIOM"
  let helperResult := LeanPaper.AxiomWalk.collect env #[`LeanPaper.AxiomWalk.collect]
  match LeanPaper.AxiomWalk.check helperResult
      [`propext, `Classical.choice, `Quot.sound] with
  | .error msg => throwError msg
  | .ok () => pure ()
  let safe := LeanPaper.AxiomWalk.collect env #[`True.intro]
  match LeanPaper.AxiomWalk.check safe [] with
  | .error msg => throwError msg
  | .ok () => pure ()
  let missing := LeanPaper.AxiomWalk.collect env #[`LeanPaper.NonexistentAuditFixture]
  unless missing.missing.contains `LeanPaper.NonexistentAuditFixture do
    throwError "REGRESSION_MISSING_CONSTANT_NOT_RECORDED"
  match LeanPaper.AxiomWalk.check missing [] with
  | .ok () => throwError "REGRESSION_INCOMPLETE_GRAPH_ACCEPTED"
  | .error _ => pure ()
  let forward := LeanPaper.AxiomWalk.collect env
    #[`AuditFixtures.S9.mk, `AuditFixtures.S9, `AuditFixtures.wrapped]
  let reverse := LeanPaper.AxiomWalk.collect env
    #[`AuditFixtures.wrapped, `AuditFixtures.S9, `AuditFixtures.S9.mk]
  unless forward.axioms.toArray.qsort Name.lt == reverse.axioms.toArray.qsort Name.lt do
    throwError "REGRESSION_ROOT_ORDER_CHANGED_UNION"
  match LeanPaper.AxiomWalk.check forward
      [`AuditFixtures.forbiddenNat, `AuditFixtures.forbiddenProof] with
  | .error msg => throwError msg
  | .ok () => pure ()
  IO.println "AXIOM_WALK_REGRESSIONS=PASS"
