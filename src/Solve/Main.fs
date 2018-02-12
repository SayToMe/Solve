namespace Solve

open TermTypes

open Rule
open Rule.Transformers

open VariableUnify
open Execute

module Solve =
    open ExpressionUnify

    let private checkAppliable (GoalSignature(name, goalArguments)) (Rule(Signature(ruleName, ruleParams), _)) =
        name = ruleName && Option.isSome(unifyParametersWithArguments ruleParams goalArguments)

    let rec solve (goal: Expression) (knowledgeBase: Rule list) =
        let rec executeCustom (goal: GoalSignature) =
            knowledgeBase
            |> List.filter (checkAppliable goal)
            |> List.toSeq
            |> Seq.collect (fun rule ->
                let (GoalSignature(_, initialArgs)) = goal
                let (Rule(Signature(_, prms), body)) = Option.get (unifyRule rule initialArgs)
                
                let initialConreceteVariables =
                    (fromArgs initialArgs, fromParams prms)
                    ||> List.map2 (fun a p ->
                        match a, p with
                        | VariableTerm _, VariableTerm _ -> None
                        | VariableTerm av, _ -> Some (av, p)
                        | _ -> None
                    )
                    |> List.collect(Option.toList)
                let initialUnconcreteVariables =
                    (fromArgs initialArgs, fromParams prms)
                    ||> List.map2 (fun a p ->
                        match a, p with
                        | VariableTerm av, VariableTerm pv -> Some (av, pv)
                        | _ -> None
                    )
                    |> List.collect(Option.toList)

                exExpr body executeCustom (fun v -> VariableTerm v)
                |> Seq.map (List.map (fun (changedVar, resTerm) ->
                    match initialUnconcreteVariables |> List.tryFind (fun (_, p) -> p = changedVar) with
                    | Some (initialVar, _) -> Some(initialVar, resTerm)
                    | _ -> None
                ) >> List.collect (Option.toList))
                |> Seq.map (List.append initialConreceteVariables)
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

