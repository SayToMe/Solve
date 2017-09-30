namespace Solve

open Types

open Rule
open Rule.Transformers

open VariableUnify
open ExpressionUnify

module Execute =
    let executeCalc =
        function
        | Value (CalcAny(AnyTyped(TypedSNumber(SNumber v1)))) -> SNumber v1
        | Plus (CalcAny(AnyTyped(TypedSNumber(SNumber v1))), CalcAny(AnyTyped(TypedSNumber(SNumber v2)))) -> SNumber <| v1 + v2
        | Subsctruct (CalcAny(AnyTyped(TypedSNumber(SNumber v1))), CalcAny(AnyTyped(TypedSNumber(SNumber v2)))) -> SNumber <| v1 - v2
        | Multiply (CalcAny(AnyTyped(TypedSNumber(SNumber v1))), CalcAny(AnyTyped(TypedSNumber(SNumber v2)))) -> SNumber <| v1 * v2
        | Division (CalcAny(AnyTyped(TypedSNumber(SNumber v1))), CalcAny(AnyTyped(TypedSNumber(SNumber v2)))) -> SNumber <| v1 / v2
        | Invert (CalcAny(AnyTyped(TypedSNumber(SNumber v1)))) -> SNumber(-v1)
        | Sqrt (CalcAny(AnyTyped(TypedSNumber(SNumber v1)))) -> SNumber <| System.Math.Sqrt v1
        | Log (CalcAny(AnyTyped(TypedSNumber(SNumber v1))), CalcAny(AnyTyped(TypedSNumber(SNumber n)))) -> SNumber <| System.Math.Log(v1, float n)
        | _ -> failwith "incorrect calc expression called"

    // TODO: maybe we should unify each time we execute expression?
    let rec executeExpression (expr: Expression) executeCustom changeVariableFn =
        let executeBinaryExpression functor condition e1 e2 =
            // Hack for equality check
            let conditionIsEquality = condition (TypedSNumber(SNumber(1.))) (TypedSNumber(SNumber(1.)))

            let e1 = changeIfVariable changeVariableFn e1
            let e2 = changeIfVariable changeVariableFn e2
            // postUnifyBinaryExpression (changeVariableFn) EqExpr e1 e2
            match (e1, e2) with
            | (AnyVariable(_), AnyVariable(_)) -> [functor(e2, e2)]
            | (AnyVariable(_), AnyTyped(_)) -> [functor(e2, e2)]
            | (AnyVariable(_), AnyStruct(_)) -> [functor(e2, e2)]
            | (AnyTyped(_), AnyVariable(_)) -> [functor(e1, e1)]
            | (AnyStruct(_), AnyVariable(_)) -> [functor(e1, e1)]
            | (AnyTyped(v1), AnyTyped(v2)) ->
                if condition v1 v2 then
                    [functor(e1, e2)]
                else
                    []
            | (AnyStruct(s1), AnyStruct(s2)) ->
                if conditionIsEquality && s1 = s2 then
                    [functor(e1, e2)]
                else
                    []
            | _ -> failwith "unexpected execute binary expression arguments"
        match expr with
        | True -> [True]
        | False -> []
        | NotExpression e -> List.map (NotExpression) (executeExpression e executeCustom changeVariableFn)
        | OrExpression (e1, e2) ->
            let first = executeExpression e1 executeCustom changeVariableFn |> List.map (fun v -> OrExpression(v, NotExecuted e2))
            let second = (executeExpression e2 executeCustom changeVariableFn |> List.map (fun x -> OrExpression(NotExecuted e1, x)))
            first@second
        | AndExpression (e1, e2) ->
            executeExpression e1 executeCustom changeVariableFn
            |> List.collect (fun _e1 ->
                getChangedVariableFns e1 _e1
                |> List.collect (fun fn ->
                    let _e2 = unifyExpression e2 fn
                    let ffn = getChangedVariableFns e2 _e2

                    ffn
                    |> List.collect (fun fn ->
                        executeExpression _e2 executeCustom fn
                        |> List.map (fun _e2res -> AndExpression(_e1, _e2res))
                    )
                )
            )
        | ResultExpression e -> [ResultExpression e]
        | CallExpression goal ->
            let (Goal(Struct(goalSign, _))) = goal
            executeCustom goal
            |> List.map (fun resExpr -> CallExpression(Goal(Struct(goalSign, resExpr))))
        | CalcExpr (v, c) ->
            let v = changeIfVariable changeVariableFn v
            let c = unifyCalc changeVariableFn c
            match v with
            | AnyVariable(_) -> [CalcExpr(AnyTyped(TypedSNumber(executeCalc c)), c)]
            | AnyTyped(TypedSNumber(v)) when v = (executeCalc c) -> [CalcExpr(AnyTyped(TypedSNumber(v)), c)]
            | _ -> []
        | EqExpr (e1, e2) -> executeBinaryExpression EqExpr (=) e1 e2
        | GrExpr (e1, e2) -> executeBinaryExpression GrExpr (>) e1 e2
        | LeExpr (e1, e2) -> executeBinaryExpression LeExpr (<) e1 e2
        | _ -> []

    // Idea is:
    // Expression is unified with arguments by parameters
    // Expression executes and all variables are resolved
    // Expression tree should be mostly unchanged
    // All changed variables can be caught afterwards
    let execute goal rule executeCustom =
        let (Goal(Struct(name, goalArguments))) = goal
        let arguments = toArgs goalArguments
        match unifyRule rule arguments with
        | Some (Rule(Signature(ruleName, unifiedRuleArgs), expr)) -> 
            if name = ruleName then
                let changeVar = List.fold2 (fun acc (Parameter(p)) (Argument(a)) -> fun v -> if AnyVariable(v) = p then a else acc v) (fun v -> AnyVariable(v)) unifiedRuleArgs arguments

                let results = executeExpression expr executeCustom changeVar
                let postResults = List.map (unifyBack (fromParams unifiedRuleArgs) expr) results
                postResults
            else
                []
        | None -> []