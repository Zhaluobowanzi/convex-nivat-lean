import StatementAudit.Bridge
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Elab.Command

open Lean Elab Command

private def moduleOf (env : Environment) (n : Name) : Name :=
  (env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!) |>.getD .anonymous

private partial def dependencyClosure (env : Environment) (pending : List Name) (seen : NameSet) : NameSet :=
  match pending with
  | [] => seen
  | n :: ns =>
    if seen.contains n then dependencyClosure env ns seen
    else
      let refs := (env.find? n).map (fun c => c.getUsedConstantsAsSet.toList) |>.getD []
      dependencyClosure env (refs ++ ns) (seen.insert n)

run_cmd do
  let env ← getEnv
  let audited := [`Nivat.convex_two_factors_nonparallel,
    `Nivat.convex_two_factors,
    `Nivat.line_horizontal,
    `Nivat.row_endpoint,
    `Nivat.convex_line_fit,
    `Nivat.convex_erosion,
    `Nivat.strict_erosion,
    `Nivat.convex_periodic_of_periodic_line_filter,
    `Nivat.convex_nivat_rational,
    `Nivat.convex_nivat,
    `Nivat.convex_two_integer_summands,
    `Nivat.convex_nivat_raw,
    `Nivat.convex_nivat_real_hull,
    `StatementAudit.RepresentativeOrigins,
    `StatementAudit.GlobalPeriod,
    `StatementAudit.RectangleStatement,
    `StatementAudit.ConvexStatement,
    `StatementAudit.HasDecomposition,
    `StatementAudit.OrderStatement,
    `StatementAudit.count_iff_representatives,
    `StatementAudit.global_iff,
    `StatementAudit.rectangle_checked,
    `StatementAudit.convex_checked,
    `StatementAudit.order_checked]
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let mut seen : NameSet := {}
  let mut rows : Array String := #[]
  for (owner, data) in env.header.moduleNames.zip env.header.moduleData do
    unless owner == `ConvexNivat || (`StatementAudit).isPrefixOf owner do continue
    for n in data.constNames do
      let some c := env.find? n | throwError "Missing compiled declaration {n}"
      let display := (privateToUserName? n).getD n
      if audited.contains display then
        seen := seen.insert display
        for ax in ← collectAxioms n do
          unless allowed.contains ax do throwError "Unexpected axiom {ax} for {display}"
      for ref in c.getUsedConstantsAsSet.toList do
        rows := rows.push s!"{n}\t{ref}\t{moduleOf env ref}"
  for n in audited do
    unless seen.contains n do throwError "Missing local declaration {n}"
  let deps := dependencyClosure env [`StatementAudit.convex_checked] {}
  for n in [`Nivat.nivat, `Nivat.nivat_rational, `NivatSubmission.nivat,
      `StatementAudit.order_checked, `Nivat.convex_two_integer_summands] do
    if deps.contains n then throwError "Unexpected dependency {n}"
  let names := deps.toList.map (fun n => (privateToUserName? n).getD n)
  for n in [`Nivat.row_endpoint, `Nivat.strict_erosion, `Nivat.convex_erosion,
      `Nivat.convex_line_fit, `Nivat.line_filter_ne_zero_of_period_divisor,
      `Nivat.Descent.complexity_descent_of_supported_multiples, `Nivat.convex_two_factors] do
    unless names.contains n do throwError "Missing expected dependency {n}"
  let output ← IO.getEnv "NIVAT_DEPENDENCY_TSV"
  if let some path := output then
    IO.FS.writeFile path ("local_declaration\tdirect_reference\treference_module\n" ++
      String.intercalate "\n" (rows.qsort (· < ·)).toList ++ "\n")
  logInfo m!"Audited {seen.size} named local declarations. Checked {rows.size} direct dependency edges and the convex theorem's dependency closure."
