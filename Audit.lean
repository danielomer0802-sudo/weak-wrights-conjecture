import OperatorPhaseRetrieval
import Lean

#print axioms OperatorPhaseRetrieval.main
#print axioms OperatorPhaseRetrieval.exists_order_three_phase_retrieval
#print axioms OperatorPhaseRetrieval.exists_near_identity_phase_retrieval
#print axioms OperatorPhaseRetrieval.exists_entire_rigid_model
#print axioms OperatorPhaseRetrieval.exists_spatial_unitary
#print axioms OperatorPhaseRetrieval.phase_retrieval_on_standardBorel
#print axioms OperatorPhaseRetrieval.phase_retrieval_on_completion
#print axioms OperatorPhaseRetrieval.main_with_instability

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (n, _) =>
    if (`OperatorPhaseRetrieval).isPrefixOf n then some n else none
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in names do
    let axioms ← collectAxioms n
    let unexpected := axioms.filter fun a => !allowed.contains a
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {n}: {unexpected}"
  IO.println s!"PASS: {names.length} declarations checked; only propext, Classical.choice, Quot.sound are allowed."
