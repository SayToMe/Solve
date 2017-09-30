namespace Solve

open Types

open Rule
open Rule.Transformers

module VariableUnify =
    let changeIfVariable changeVariable =
        function
        | AnyVariable(v) -> changeVariable v
        | a -> a

    let processStruct changeVariable (Struct(functor, prms)) =
        Struct(functor, prms |> List.map (changeIfVariable changeVariable))

    let rec unifyTwoAny v1 v2 =
        match (v1, v2) with
        | (AnyVariable(_), AnyVariable(_)) -> Some v1
        | (AnyVariable(_), AnyTyped(_)) -> Some v2
        | (AnyVariable(_), AnyStruct(_)) -> Some v2
        | (AnyTyped(_), AnyVariable(_)) -> Some v1
        | (AnyStruct(_), AnyVariable(_)) -> Some v1
        | (AnyTyped(vt1), AnyTyped(vt2)) when vt1 = vt2 -> Some v2
        | (AnyStruct(Struct(f1, p1)), AnyStruct(Struct(f2, p2))) when f1 = f2 && p1.Length = p2.Length ->
            let newArgs = List.map2 (fun v1 v2 -> unifyTwoAny v1 v2) p1 p2
            if List.exists Option.isNone newArgs then
                None
            else
                let newArgs = newArgs |> List.map Option.get
                Some(AnyStruct(Struct(f1, newArgs)))
        | _ -> None

    let postUnifyBinaryExpression proc functor e1 e2 =
        match (e1, e2) with
        | (AnyVariable(v1), AnyVariable(v2)) -> functor(proc v1, proc v2)
        | (AnyVariable(v1), AnyTyped(_)) -> functor(proc v1, e2)
        | (AnyVariable(v1), AnyStruct(v2)) -> functor(proc v1, AnyStruct(processStruct proc v2))
        | (AnyTyped(_), AnyVariable(v2)) -> functor(e1, proc v2)
        | (AnyStruct(v1), AnyVariable(v2)) -> functor(AnyStruct(processStruct proc v1), proc v2)
        | _ -> functor(e1, e2)

    let postUnifyUnaryExpressions v1 v2 fn v =
        if AnyVariable(v) = v1 then 
            v2 
        else 
            fn v

    let postUnifyBinaryExpressions (v1, v2) (v3, v4) fn v =
        if AnyVariable(v) = v1 then
            v3 
        else if AnyVariable(v) = v2 then 
            v4 
        else fn v
        
    let rec unifyParamsWithArguments parameters arguments =
        let prms = List.map2 (fun (Parameter(p)) (Argument(a)) -> unifyTwoAny p a) parameters arguments
        if List.exists Option.isNone prms then
            None
        else
            Some <| List.map Option.get prms

module ExpressionUnify =
    open VariableUnify

    let rec unifyCalc changeVariable v =
        let rec changeCalcTermIfVariable =
            function
            | CalcInner c -> CalcInner(unifyCalc changeVariable c)
            | CalcAny(AnyVariable(v)) -> CalcAny(changeVariable v)
            | CalcAny(AnyTyped(v)) -> CalcAny(AnyTyped(v))
            | CalcAny(AnyStruct(v)) -> CalcAny(AnyStruct(processStruct changeVariable v))
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
        | NotExpression e -> NotExpression (unifyExpression e changeVariable)
        | OrExpression (e1, e2) -> OrExpression(unifyExpression e1 changeVariable, unifyExpression e2 changeVariable)
        | AndExpression (e1, e2) -> AndExpression(unifyExpression e1 changeVariable, unifyExpression e2 changeVariable)
        | ResultExpression e ->
            match e with
            | AnyVariable v -> ResultExpression (changeVariable v)
            | AnyTyped _ -> expression
            | AnyStruct(v) -> ResultExpression(AnyStruct(processStruct changeVariable v))
        | CallExpression goal ->
            let (Goal(Struct(goalName, arguments))) = goal
            let newGoalArgs =
                List.map (function
                            | AnyVariable(v) -> Argument(changeVariable v)
                            | AnyTyped(v) -> Argument(AnyTyped(v))
                            | AnyStruct(v) -> Argument(AnyStruct(processStruct changeVariable v))) arguments
            CallExpression (Goal(Struct(goalName, fromArgs newGoalArgs)))
        | CalcExpr (v, c) ->
            match v with
            | AnyVariable(vv) -> CalcExpr(changeVariable vv, unifyCalc changeVariable c)
            | AnyTyped(v) -> CalcExpr(AnyTyped(v), unifyCalc changeVariable c)
            | AnyStruct _ -> failwith "Calc of custom struct is not implemented yet"
        | EqExpr (e1, e2) -> postUnifyBinaryExpression changeVariable EqExpr e1 e2
        | GrExpr (e1, e2) -> postUnifyBinaryExpression changeVariable GrExpr e1 e2
        | LeExpr (e1, e2) -> postUnifyBinaryExpression changeVariable LeExpr e1 e2
        | _ -> failwith "unchecked something"

    // returns change variable functions according to execution branches
    let getChangedVariableFns initialExpression expression =
        let rec _getChangedVariableFn initialExpression expression (changedVariableFns: (Variable -> Any) list) =
            match (initialExpression, expression) with
            | (True, True) -> changedVariableFns
            | (False, False) -> changedVariableFns
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
            | (CallExpression(goal1), CallExpression(goal2)) ->
                let (Goal(Struct(name1, goalArgs1))) = goal1
                let (Goal(Struct(name2, goalArgs2))) = goal2
                if name1 = name2 then
                    List.map (fun fn -> List.fold2 (fun fns a1 a2 -> postUnifyUnaryExpressions a1 a2 fns) fn goalArgs1 goalArgs2) changedVariableFns
                else
                    failwith ""
            | (CalcExpr(v1, _), CalcExpr(v2, _)) -> changedVariableFns |> List.map (postUnifyUnaryExpressions v1 v2)
            | (EqExpr(v1, v2), EqExpr(v3, v4)) -> changedVariableFns |> List.map (postUnifyBinaryExpressions (v1, v2) (v3, v4))
            | (GrExpr(v1, v2), GrExpr(v3, v4)) -> changedVariableFns |> List.map (postUnifyBinaryExpressions (v1, v2) (v3, v4))
            | (LeExpr(v1, v2), LeExpr(v3, v4)) -> changedVariableFns |> List.map (postUnifyBinaryExpressions (v1, v2) (v3, v4))
            | _ -> failwithf "failed to getChangedVariableFn result. %O != %O" initialExpression expression
        _getChangedVariableFn initialExpression expression [(fun v -> AnyVariable(v))]
        
    let unifyExpressionByParams parameters arguments expression =
        let changeVariable (Parameter(p)) a =
            let retIfEquals variable result v = if v = variable then result else AnyVariable(v)
            match (p, a) with
            | AnyVariable(v1), AnyVariable(v2) -> fun v -> if v = v2 then AnyVariable v1 else AnyVariable v
            | AnyVariable(v1), AnyTyped(_) -> retIfEquals v1 a
            | AnyVariable(v1), AnyStruct(_) -> retIfEquals v1 a
            | AnyTyped(_), AnyVariable(v2) -> retIfEquals v2 p
            | AnyStruct(_), AnyVariable(v2) -> retIfEquals v2 p
            | _ -> fun x -> AnyVariable x

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
        | (_, NotExecuted _) -> arguments
        | (NotExpression e1, NotExpression e2) -> unifyBack arguments e1 e2
        | (OrExpression(e1, e2), OrExpression(e3, e4)) -> unifyBack (unifyBack arguments e1 e3) e2 e4
        | (AndExpression(e1, e2), AndExpression(e3, e4)) -> unifyBack (unifyBack arguments e1 e3) e2 e4
        | (ResultExpression e1, ResultExpression e2) -> arguments |> List.map (fun a -> if a = e1 then e2 else a)
        | (CallExpression(goal1), CallExpression(goal2)) ->
            let (Goal(Struct(name1, goalArgs1))) = goal1
            let (Goal(Struct(name2, goalArgs2))) = goal2
            if name1 = name2 then
                List.fold2 (fun args (arg1) (arg2) -> unifyWithArgs args arg1 arg2) arguments goalArgs1 goalArgs2
            else 
                failwith ""
        | (CalcExpr(v1, _), CalcExpr(v2, _)) -> unifyWithArgs arguments v1 v2
        | (EqExpr(v1, v2), EqExpr(v3, v4)) -> unifyWithArgs (unifyWithArgs arguments v1 v3) v2 v4
        | (GrExpr(v1, v2), GrExpr(v3, v4)) -> unifyWithArgs (unifyWithArgs arguments v1 v3) v2 v4
        | (LeExpr(v1, v2), LeExpr(v3, v4)) -> unifyWithArgs (unifyWithArgs arguments v1 v3) v2 v4
        | _ -> failwithf "failed to unify result. %O != %O" initialExpression expression
