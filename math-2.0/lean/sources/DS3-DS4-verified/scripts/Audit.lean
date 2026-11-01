public meta import Lean

/-!
The Python runner prepends imports for every local library module. Audit by
module provenance, not declaration namespace, so private helpers and declarations
outside the MathResearch namespace are included as well.
-/

public meta section

open Lean Elab Command

elab "#audit_math_research" : command => do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  let mut rejected := false
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    let modString := mod.toString
    unless modString == "MathResearch" || modString.startsWith "MathResearch." do
      continue
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun ax => !allowed.contains ax
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .axiomInfo _ => "axiom"
      | _ => "definition-or-generated"
    let row := Json.mkObj [
      ("declaration", toJson name.toString),
      ("module", toJson modString),
      ("kind", toJson kind),
      ("axioms", toJson (axioms.map Name.toString)),
      ("unexpected_axioms", toJson (unexpected.map Name.toString))]
    liftIO <| IO.println ("MATH_RESEARCH_AUDIT " ++ row.compress)
    count := count + 1
    unless unexpected.isEmpty do
      rejected := true
  if count == 0 then
    throwError "No project declarations were audited"
  if rejected then
    throwError "Project declarations use unfinished proofs or additional axioms; see audit output"

#audit_math_research
