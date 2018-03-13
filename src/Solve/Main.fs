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
                        let rec getConcreteVars a p =
                            match a, p with
                            | VariableTerm _, VariableTerm _ -> []
                            | VariableTerm av, _ -> [av, p]
                            | ListTerm l1, ListTerm l2 ->
                                match l1, l2 with
                                | TypedListTerm(h1, r1), TypedListTerm(h2, r2) ->
                                    (getConcreteVars h1 h2) @ (getConcreteVars (ListTerm r1) (ListTerm r2))
                                | VarListTerm(v1), NilTerm -> [v1, ListTerm(NilTerm)]
                                | VarListTerm(v1), TypedListTerm(_,_) -> [v1, p]
                                | _ -> []
                            | _ -> []
                        getConcreteVars a p
                    ) |> List.collect (fun x -> x)
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
                |> Seq.map (List.filter (fun vt -> 
                    match vt with
                    | (v1, VariableTerm(v2)) when v1 = v2 -> false
                    | _ -> true))
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
