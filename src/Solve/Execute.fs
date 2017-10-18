namespace Solve

open TermTypes

open Rule
open Rule.Transformers

open VariableUnify
open ExpressionUnify

module Execute =
    let rec executeCalc =
        function
        | Value (CalcAny(TypedTerm(TypedNumberTerm(NumberTerm v1)))) -> NumberTerm v1
        | Value (CalcAny(StructureTerm(Structure(functor, args)))) ->
            match functor with
            | "+" when args.Length = 2 -> executeCalc (Plus(CalcAny(args.[0]), CalcAny(args.[1])))
            | "-" when args.Length = 2 -> executeCalc (Subsctruct(CalcAny(args.[0]), CalcAny(args.[1])))
            | "*" when args.Length = 2 -> executeCalc (Multiply(CalcAny(args.[0]), CalcAny(args.[1])))
            | "/" when args.Length = 2 -> executeCalc (Division(CalcAny(args.[0]), CalcAny(args.[1])))
            | "-" when args.Length = 1 -> executeCalc (Invert(CalcAny(args.[0])))
            | "sqrt" when args.Length = 1 -> executeCalc (Sqrt(CalcAny(args.[0])))
            | "log" when args.Length = 2 -> executeCalc (Log(CalcAny(args.[0]), CalcAny(args.[1])))
            | _ -> failwith "Cant find according calc functor"
        | Plus (CalcAny(TypedTerm(TypedNumberTerm(NumberTerm v1))), CalcAny(TypedTerm(TypedNumberTerm(NumberTerm v2)))) -> NumberTerm <| v1 + v2
        | Subsctruct (CalcAny(TypedTerm(TypedNumberTerm(NumberTerm v1))), CalcAny(TypedTerm(TypedNumberTerm(NumberTerm v2)))) -> NumberTerm <| v1 - v2
        | Multiply (CalcAny(TypedTerm(TypedNumberTerm(NumberTerm v1))), CalcAny(TypedTerm(TypedNumberTerm(NumberTerm v2)))) -> NumberTerm <| v1 * v2
        | Division (CalcAny(TypedTerm(TypedNumberTerm(NumberTerm v1))), CalcAny(TypedTerm(TypedNumberTerm(NumberTerm v2)))) -> NumberTerm <| v1 / v2
        | Invert (CalcAny(TypedTerm(TypedNumberTerm(NumberTerm v1)))) -> NumberTerm(-v1)
        | Sqrt (CalcAny(TypedTerm(TypedNumberTerm(NumberTerm v1)))) -> NumberTerm <| System.Math.Sqrt v1
        | Log (CalcAny(TypedTerm(TypedNumberTerm(NumberTerm v1))), CalcAny(TypedTerm(TypedNumberTerm(NumberTerm n)))) -> NumberTerm <| System.Math.Log(v1, float n)
        | _ -> failwith "incorrect calc expression called"

    // TODO: maybe we should unify each time we execute expression?
    let rec executeExpression (expr: Expression) executeCustom changeVariableFn =
        let keepFirstCut exprs =
            match Seq.tryFind (function | Cut -> true | _ -> false) exprs with
            | Some v -> Seq.singleton v
            | None -> exprs
        let changeIfVariable changeVariable =
            function
            | VariableTerm(v) -> changeVariable v
            | a -> a
        let executeBinaryExpression functor condition e1 e2 =
            // Hack for equality check
            let conditionIsEquality = condition (TypedNumberTerm(NumberTerm(1.))) (TypedNumberTerm(NumberTerm(1.)))

            let e1 = changeIfVariable changeVariableFn e1
            let e2 = changeIfVariable changeVariableFn e2
            match (e1, e2) with
            | (VariableTerm(_), VariableTerm(_)) -> Seq.singleton (functor(e2, e2))
            | (VariableTerm(_), TypedTerm(_)) -> Seq.singleton (functor(e2, e2))
            | (VariableTerm(_), StructureTerm(_)) -> Seq.singleton (functor(e2, e2))
            | (TypedTerm(_), VariableTerm(_)) -> Seq.singleton (functor(e1, e1))
            | (StructureTerm(_), VariableTerm(_)) -> Seq.singleton (functor(e1, e1))
            | (TypedTerm(v1), TypedTerm(v2)) ->
                if condition v1 v2 then
                    Seq.singleton (functor(e1, e2))
                else
                    Seq.empty
            | (StructureTerm(s1), StructureTerm(s2)) ->
                if conditionIsEquality && s1 = s2 then
                    Seq.singleton (functor(e1, e2))
                else
                    Seq.empty
            | _ -> failwith "unexpected execute binary expression arguments"
        match expr with
        | True -> Seq.singleton True
        | False -> Seq.empty
        | Cut -> Seq.singleton Cut
        | NotExpression e -> Seq.map (NotExpression) (executeExpression e executeCustom changeVariableFn)
        | OrExpression (e1, e2) ->
            let first = executeExpression e1 executeCustom changeVariableFn |> Seq.map (fun v -> OrExpression(v, NotExecuted e2)) |> keepFirstCut
            let second = (executeExpression e2 executeCustom changeVariableFn |> Seq.map (fun x -> OrExpression(NotExecuted e1, x))) |> keepFirstCut
            Seq.append first second
        | AndExpression (e1, e2) ->
            executeExpression e1 executeCustom changeVariableFn |> keepFirstCut
            |> Seq.collect (fun _e1 ->
                getChangedVariableFns e1 _e1
                |> Seq.collect (fun fn ->
                    let _e2 = unifyExpression e2 fn
                    let ffn = getChangedVariableFns e2 _e2

                    ffn
                    |> Seq.collect (fun fn ->
                        executeExpression _e2 executeCustom fn
                        |> Seq.map (fun _e2res -> AndExpression(_e1, _e2res)) |> keepFirstCut
                    )
                )
            )
        | ResultExpression e -> Seq.singleton (ResultExpression e)
        | CallExpression goal ->
            let (Goal(Structure(goalSign, _))) = goal
            executeCustom goal
            |> Seq.map (fun resExpr -> CallExpression(Goal(Structure(goalSign, resExpr))))
        | CalcExpr (v, c) ->
            let v = changeIfVariable changeVariableFn v
            let c = unifyCalc changeVariableFn c
            match v with
            | VariableTerm(_) -> Seq.singleton (CalcExpr(TypedTerm(TypedNumberTerm(executeCalc c)), c))
            | TypedTerm(TypedNumberTerm(v)) when v = (executeCalc c) -> Seq.singleton (CalcExpr(TypedTerm(TypedNumberTerm(v)), c))
            | _ -> Seq.empty
        | EqExpr (e1, e2) -> executeBinaryExpression EqExpr (=) e1 e2
        | GrExpr (e1, e2) -> executeBinaryExpression GrExpr (>) e1 e2
        | LeExpr (e1, e2) -> executeBinaryExpression LeExpr (<) e1 e2
        | _ -> Seq.empty

    // Idea is:
    // Expression is unified with arguments by parameters
    // Expression executes and all variables are resolved
    // Expression tree should be mostly unchanged
    // All changed variables can be caught afterwards
    let execute (Goal(Structure(name, goalArguments))) rule executeCustom =
        let arguments = toArgs goalArguments
        match unifyRule rule arguments with
        | Some (Rule(Signature(ruleName, unifiedRuleArgs), expr)) -> 
            if name = ruleName then
                let changeVar = List.fold2 (fun acc (Parameter(p)) (Argument(a)) -> fun v -> if VariableTerm(v) = p then a else acc v) (fun v -> VariableTerm(v)) unifiedRuleArgs arguments

                let results = executeExpression expr executeCustom changeVar
                let postResults = Seq.map (unifyBack (fromParams unifiedRuleArgs) expr) results
                postResults
            else
                Seq.empty
        | None -> Seq.empty