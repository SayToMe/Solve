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
            |> List.toSeq
            |> Seq.filter (checkAppliable goal)
            |> Seq.collect (fun rule ->
                let (GoalSignature(_, initialArgs)) = goal
                let (Rule(Signature(_, parameters), body)) = Option.get (unifyRule rule initialArgs)
                
                let initialConreceteVariables =
                    (fromArgs initialArgs, fromParams parameters)
                    ||> List.map2 (fun argument parameter ->
                        let rec getConcreteVars argument parameter =
                            match argument, parameter with
                            | VariableTerm _, VariableTerm _ -> []
                            | VariableTerm leftVariable, _ -> [leftVariable, parameter]
                            | ListTerm leftList, ListTerm rightList ->
                                match leftList, rightList with
                                | TypedListTerm(leftTerm, leftTail), TypedListTerm(rightTerm, rightTail) ->
                                    (getConcreteVars leftTerm rightTerm) @ (getConcreteVars (ListTerm leftTail) (ListTerm rightTail))
                                | VarListTerm(leftVariableListTerm), NilTerm -> [leftVariableListTerm, ListTerm(NilTerm)]
                                | VarListTerm(leftVariableListTerm), TypedListTerm(_,_) -> [leftVariableListTerm, parameter]
                                | _ -> []
                            | _ -> []
                        getConcreteVars argument parameter
                    ) |> List.collect id
                let initialUnconcreteVariables =
                    (fromArgs initialArgs, fromParams parameters)
                    ||> List.map2 (fun argument parameter ->
                        match argument, parameter with
                        | VariableTerm leftVariableTerm, VariableTerm rightVariableTerm -> Some (leftVariableTerm, rightVariableTerm)
                        | _ -> None
                    )
                    |> List.collect(Option.toList)

                exExpr body executeCustom VariableTerm
                |> Seq.map (List.map (fun (changedVar, resTerm) ->
                    match initialUnconcreteVariables |> List.tryFind (fun (_, parameter) -> parameter = changedVar) with
                    | Some (initialVar, _) -> Some(initialVar, resTerm)
                    | _ -> None
                ) >> List.collect (Option.toList))
                |> Seq.map (List.append initialConreceteVariables)
                |> Seq.map (List.filter (fun variableTermPair -> 
                    match variableTermPair with
                    | (leftTerm, VariableTerm(rightVariableTerm)) when leftTerm = rightVariableTerm -> false
                    | _ -> true))
            )
            |> Seq.map (fun changes ->
                let (GoalSignature(_, initialArgs)) = goal
                initialArgs
                |> List.map (fun (Argument(argumentTerm)) ->
                    match changes |> List.tryFind (fun (variable, _) -> VariableTerm(variable) = argumentTerm) with
                    | Some (_, res) -> res
                    | None -> argumentTerm
                )
            )

        exExpr goal executeCustom VariableTerm
