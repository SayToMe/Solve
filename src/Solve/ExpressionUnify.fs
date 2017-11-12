namespace Solve

open TermTypes

open Rule
open Rule.Transformers
open VariableUnify

module ExpressionUnify =
    open VariableUnify

    let rec unifyCalc changeVariable v =
        let rec changeCalcTermIfVariable =
            function
            | CalcInner c -> CalcInner(unifyCalc changeVariable c)
            | CalcAny(VariableTerm(v)) -> CalcAny(changeVariable v)
            | CalcAny(TypedTerm(v)) -> CalcAny(TypedTerm(v))
            | CalcAny(StructureTerm(v)) -> CalcAny(StructureTerm(processStruct changeVariable v))
        match v with
        | Plus (v1, v2) -> Plus(changeCalcTermIfVariable v1, changeCalcTermIfVariable v2)
        | Subsctruct (v1, v2) -> Subsctruct(changeCalcTermIfVariable v1, changeCalcTermIfVariable v2)
        | Multiply (v1, v2) -> Multiply(changeCalcTermIfVariable v1, changeCalcTermIfVariable v2)
        | Division (v1, v2) -> Division(changeCalcTermIfVariable v1, changeCalcTermIfVariable v2)
        | Invert (v1) -> Invert(changeCalcTermIfVariable v1)
        | Sqrt (v1) -> Sqrt(changeCalcTermIfVariable v1)
        | Log (v1, n) -> Log(changeCalcTermIfVariable v1, changeCalcTermIfVariable n)
        | Value(v) -> Value(changeCalcTermIfVariable v)

    let rec unifyExpression expression changeVariable =
        match expression with
        | True -> True
        | False -> False
        | Cut -> Cut
        | NotExpression e -> NotExpression (unifyExpression e changeVariable)
        | OrExpression (e1, e2) -> OrExpression(unifyExpression e1 changeVariable, unifyExpression e2 changeVariable)
        | AndExpression (e1, e2) -> AndExpression(unifyExpression e1 changeVariable, unifyExpression e2 changeVariable)
        | ResultExpression e ->
            match e with
            | VariableTerm v -> ResultExpression (changeVariable v)
            | TypedTerm _ -> expression
            | StructureTerm(v) -> ResultExpression(StructureTerm(processStruct changeVariable v))
        | CallExpression(Goal(Structure(goalName, arguments))) ->
            let newGoalArgs =
                List.map (function
                            | VariableTerm(v) -> Argument(changeVariable v)
                            | TypedTerm(v) -> Argument(TypedTerm(v))
                            | StructureTerm(v) -> Argument(StructureTerm(processStruct changeVariable v))) arguments
            CallExpression (Goal(Structure(goalName, fromArgs newGoalArgs)))
        | CalcExpr (v, c) ->
            match v with
            | VariableTerm(vv) -> CalcExpr(changeVariable vv, unifyCalc changeVariable c)
            | TypedTerm(v) -> CalcExpr(TypedTerm(v), unifyCalc changeVariable c)
            | StructureTerm _ -> failwith "Calc of custom struct is not implemented yet"
        | EqExpr (e1, e2) -> postUnifyBinaryExpression changeVariable EqExpr e1 e2
        | GrExpr (e1, e2) -> postUnifyBinaryExpression changeVariable GrExpr e1 e2
        | LeExpr (e1, e2) -> postUnifyBinaryExpression changeVariable LeExpr e1 e2
        | _ -> failwith "unchecked something"

    // returns change variable functions according to execution branches
    let getChangedVariableFns initialExpression expression =
        let rec _getChangedVariableFn initialExpression expression (changedVariableFns: (Variable -> Term) list) =
            match (initialExpression, expression) with
            | (True, True) -> changedVariableFns
            | (False, False) -> changedVariableFns
            | (Cut, Cut) -> changedVariableFns
            | (_, NotExecuted _) -> changedVariableFns
            | (NotExpression e1, NotExpression e2) -> _getChangedVariableFn e1 e2 changedVariableFns
            | (OrExpression(e1, e2), OrExpression(e3, e4)) ->
                let changedFn1 = _getChangedVariableFn e1 e3 changedVariableFns
                let changedFn2 = _getChangedVariableFn e2 e4 changedVariableFns
                changedFn1@changedFn2
            | (AndExpression(e1, e2), AndExpression(e3, e4)) ->
                let changedFn1 = _getChangedVariableFn e1 e3 changedVariableFns
                let changedFn2 = _getChangedVariableFn e2 e4 changedFn1
                changedFn2
            | (ResultExpression e1, ResultExpression e2) -> changedVariableFns |> List.map (postUnifyUnaryExpressions e1 e2)
            | (CallExpression(Goal(Structure(name1, goalArgs1))), CallExpression(Goal(Structure(name2, goalArgs2)))) when name1 = name2 && goalArgs1.Length = goalArgs2.Length ->
                List.map (fun fn -> List.fold2 (fun fns a1 a2 -> postUnifyUnaryExpressions a1 a2 fns) fn goalArgs1 goalArgs2) changedVariableFns
            | (CalcExpr(v1, _), CalcExpr(v2, _)) -> changedVariableFns |> List.map (postUnifyUnaryExpressions v1 v2)
            | (EqExpr(v1, v2), EqExpr(v3, v4)) -> changedVariableFns |> List.map (postUnifyBinaryExpressions (v1, v2) (v3, v4))
            | (GrExpr(v1, v2), GrExpr(v3, v4)) -> changedVariableFns |> List.map (postUnifyBinaryExpressions (v1, v2) (v3, v4))
            | (LeExpr(v1, v2), LeExpr(v3, v4)) -> changedVariableFns |> List.map (postUnifyBinaryExpressions (v1, v2) (v3, v4))
            | _ -> failwithf "failed to getChangedVariableFn result. %O != %O" initialExpression expression
        _getChangedVariableFn initialExpression expression [(fun v -> VariableTerm(v))]
        
    let unifyExpressionByParams parameters arguments expression =
        let changeVariable (Parameter(p)) a =
            let retIfEquals variable result v = if v = variable then result else VariableTerm(v)
            match (p, a) with
            | VariableTerm(v1), VariableTerm(v2) -> fun v -> if v = v2 then VariableTerm v1 else VariableTerm v
            | VariableTerm(v1), TypedTerm(_) -> retIfEquals v1 a
            | VariableTerm(v1), StructureTerm(_) -> retIfEquals v1 a
            | TypedTerm(_), VariableTerm(v2) -> retIfEquals v2 p
            | StructureTerm(_), VariableTerm(v2) -> retIfEquals v2 p
            | _ -> fun x -> VariableTerm x

        unifyParamsWithArguments parameters arguments
        |> Option.bind (fun unifiedArgs ->
            let newExpr = 
                List.zip parameters unifiedArgs
                |> List.fold (fun acc (p, b) -> unifyExpression acc (changeVariable p b)) expression
            (newExpr, unifiedArgs)
            |> Some)

    let unifyRule (Rule(Signature(name, parameters), body)) arguments =
        unifyExpressionByParams parameters arguments body
        |> Option.bind (fun (resultBody, resultParameters) -> Some(Rule(Signature(name, toParams resultParameters), resultBody)))
    
    let rec unifyBack arguments initialExpression expression =
        let unifyWithArgs args v1 v2 = args |> List.map (fun (a) -> if a = v1 then v2 else a)

        match (initialExpression, expression) with
        | (True, True) -> arguments
        | (False, False) -> []
        | (Cut, Cut) -> arguments
        | (_, NotExecuted _) -> arguments
        | (NotExpression e1, NotExpression e2) -> unifyBack arguments e1 e2
        | (OrExpression(e1, e2), OrExpression(e3, e4)) -> unifyBack (unifyBack arguments e1 e3) e2 e4
        | (AndExpression(e1, e2), AndExpression(e3, e4)) -> unifyBack (unifyBack arguments e1 e3) e2 e4
        | (ResultExpression e1, ResultExpression e2) -> arguments |> List.map (fun a -> if a = e1 then e2 else a)
        | (CallExpression(Goal(Structure(name1, goalArgs1))), CallExpression(Goal(Structure(name2, goalArgs2)))) when name1 = name2 && goalArgs1.Length = goalArgs2.Length ->
            List.fold2 (fun args (arg1) (arg2) -> unifyWithArgs args arg1 arg2) arguments goalArgs1 goalArgs2
        | (CalcExpr(v1, _), CalcExpr(v2, _)) -> unifyWithArgs arguments v1 v2
        | (EqExpr(v1, v2), EqExpr(v3, v4)) -> unifyWithArgs (unifyWithArgs arguments v1 v3) v2 v4
        | (GrExpr(v1, v2), GrExpr(v3, v4)) -> unifyWithArgs (unifyWithArgs arguments v1 v3) v2 v4
        | (LeExpr(v1, v2), LeExpr(v3, v4)) -> unifyWithArgs (unifyWithArgs arguments v1 v3) v2 v4
        | _ -> failwithf "failed to unify result. %O != %O" initialExpression expression