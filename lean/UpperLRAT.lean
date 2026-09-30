import Mathlib.Tactic.Sat.FromLRAT

/-! A small command exposing Mathlib's kernel-checked LRAT theorem directly.
The parser and reconstruction code produce ordinary proof terms. The command
adds no axiom and does not use native_decide or trust the SAT solver. -/
open Lean Elab Command

elab "checked_lrat " ctx:ident proof:ident cnf:str lrat:str : command => do
  let ns ← getCurrNamespace
  let ctxName := ns ++ ctx.getId
  let proofName := ns ++ proof.getId
  liftTermElabM do
    let (_, context, _, certificate) ← Mathlib.Tactic.Sat.fromLRATAux
      cnf.getString lrat.getString proofName
    addDecl <| Declaration.defnDecl {
      name := ctxName, levelParams := [], type := mkConst ``Sat.Fmla,
      value := context, hints := .regular 0, safety := .safe }
    addDecl <| Declaration.thmDecl {
      name := proofName, levelParams := [],
      type := mkApp2 (mkConst ``Sat.Fmla.proof) (mkConst ctxName) (mkConst ``Sat.Clause.nil),
      value := certificate }

namespace LittlewoodCylinders.Upper.SAT.LRATSanity

checked_lrat context contradiction
  "p cnf 2 4 1 2 0 -1 2 0 1 -2 0 -1 -2 0"
  "5 -2 0 4 3 0 5 d 3 4 0 6 1 0 5 1 0 6 d 1 0 7 0 5 2 6 0"

#print axioms contradiction

end LittlewoodCylinders.Upper.SAT.LRATSanity
