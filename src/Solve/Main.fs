namespace Solve

open TermTypes

open Rule
open Rule.Transformers

open VariableUnify
open Execute

module Solve =
    let private checkAppliable (GoalSignature(name, goalArguments)) (Rule(Signature(ruleName, ruleParams), _)) =
        name = ruleName && Option.isSome(unifyParametersWithArguments ruleParams goalArguments)

    let rec solve (goal: Expression) (knowledgeBase: Rule list) =
        let rec executeCustom (goal: GoalSignature) =
            knowledgeBase
            |> List.filter (checkAppliable goal)
            |> List.toSeq
            |> Seq.collect (fun (Rule(_, body)) -> 
                exExpr body executeCustom (fun v -> VariableTerm v)
            )
            |> Seq.map (fun changes ->
                let (GoalSignature(_, initialArgs)) = goal
                initialArgs
                |> List.map (fun (Argument(a)) ->
                    match changes |> List.tryFind (fun (v, _) -> VariableTerm(v) = a) with
                    | Some (_, res) -> res
                    | None -> a
                )
            )

        exExpr goal executeCustom (fun v -> VariableTerm(v))

