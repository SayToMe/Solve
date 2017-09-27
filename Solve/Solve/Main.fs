namespace Solve

open System.Diagnostics

[<AutoOpen>]
module STypes =
    [<AutoOpen>]
    module Concrete =
        type SBool = SBool of bool
        type SNumber = SNumber of double
        type SChar = SChar of char
    
        type SList = SList of list<Typed>
        and Typed = TypedSBool of SBool | TypedSNumber of SNumber | TypedSChar of SChar | TypedSList of SList

    [<AutoOpen>]
    module Another =
        type AnonimVariable = AnonimVariable
        type Variable = Variable of string
        
    [<StructuredFormatDisplay("{AsString}")>]
    type Any = AnyVariable of Variable | AnyTyped of Typed | AnyStruct of Struct
        with
        member a.AsString =
            match a with
            | AnyVariable(Variable(v)) -> "~" + v + "~"
            | AnyTyped(typed) ->
                let rec formatTyped = function
                                      | TypedSBool(SBool v) -> v.ToString()
                                      | TypedSNumber(SNumber v) -> v.ToString()
                                      | TypedSChar(SChar v) -> v.ToString()
                                      | TypedSList(SList v) when List.forall (function | TypedSChar (_) -> true | _ -> false) v -> "[" + (List.fold (fun acc s -> if acc = "" then formatTyped s else acc + formatTyped s) "" v) + "]"
                                      | TypedSList(SList v) -> "[" + (List.fold (fun acc s -> if acc = "" then formatTyped s else acc + ", " + formatTyped s) "" v) + "]"
                formatTyped typed

type Argument = Argument of Any

type Parameter = Parameter of Any

type Signature = Signature of string * Parameter list
type Goal = Goal of string * Argument list

[<AutoOpenAttribute>]
module CalcModule =
    type Calc =
        | Value of CalcTerm
        | Plus of CalcTerm * CalcTerm
        | Subsctruct of CalcTerm * CalcTerm
        | Invert of CalcTerm
        | Multiply of CalcTerm * CalcTerm
        | Division of CalcTerm * CalcTerm
        | Sqrt of CalcTerm
        | Log of CalcTerm * CalcTerm
    and CalcTerm = CalcAny of Any | CalcInner of Calc

type Expression =
    | True
    | False
    | NotExecuted of Expression
    | NotExpression of Expression
    | OrExpression of Expression * Expression
    | AndExpression of Expression * Expression
    | ResultExpression of Any
    | CallExpression of Goal
    | CalcExpr of Any * Calc
    | EqExpr of Any * Any
    | GrExpr of Any * Any
    | LeExpr of Any * Any
and Rule = Rule of Signature * Expression

type Result = Any list list

[<AutoOpen>]
module MainModule =
    [<DebuggerStepThrough>]
    let variable (name: string) = AnyVariable (Variable name)
    [<DebuggerStepThrough>]
    let resv v = ResultExpression (AnyVariable v)
    [<DebuggerStepThrough>]
    let res t = ResultExpression (AnyTyped t)
    [<DebuggerStepThrough>]
    let resa a = ResultExpression a
    [<DebuggerStepThrough>]
    let resp = function
        | Parameter(AnyVariable v) -> resv v
        | Parameter(AnyTyped v) -> res v

    [<DebuggerStepThrough>]
    let signature (name: string) (prms: Any list) =
        Signature (name, List.map Parameter prms)
    
    [<DebuggerStepThrough>]    
    let fromArgs = List.map (fun (Argument(a)) -> a)
    [<DebuggerStepThrough>]
    let toArgs = List.map (fun a -> Argument(a))

    [<DebuggerStepThrough>]
    let fromParams = List.map (fun (Parameter(a)) -> a)
    [<DebuggerStepThrough>]
    let toParams = List.map (fun a -> Parameter(a))

    [<DebuggerStepThrough>]
    let sbool v = TypedSBool <| SBool v
    [<DebuggerStepThrough>]
    let strue = sbool true
    [<DebuggerStepThrough>]
    let sfalse = sbool false

    [<DebuggerStepThrough>]
    let snum v = TypedSNumber <| SNumber v
    [<DebuggerStepThrough>]
    let snum1 = snum 1.

    [<DebuggerStepThrough>]
    let schar v = TypedSChar <| SChar v

    [<DebuggerStepThrough>]
    let formatResult (result: Result) =
        let format fn =
            function
            | [] -> "[]"
            | [h] -> "[" + fn h + "]"
            | list -> "[" + (List.fold (fun acc n -> if acc = "" then fn n else acc + ", " + fn n) "" list) + "]"
        format (format (fun (a: Any) -> a.AsString)) result

    [<DebuggerStepThrough>]
    let (=>) sign body = Rule (sign, body)
    [<DebuggerStepThrough>]
    let (/=>) name variables = signature name variables
    [<DebuggerStepThrough>]
    let (/|) expr1 expr2 = OrExpression (expr1, expr2)
    [<DebuggerStepThrough>]
    let (/&) expr1 expr2 = AndExpression (expr1, expr2)

    [<DebuggerStepThrough>]
    let (/=) e1 e2 = EqExpr (e1, e2)
    [<DebuggerStepThrough>]
    let (/>) e1 e2 = GrExpr (e1, e2)
    [<DebuggerStepThrough>]
    let (/<) e1 e2 = LeExpr (e1, e2)

    [<DebuggerStepThrough>]
    let valp = function
        | Parameter(AnyTyped(TypedSNumber(v))) -> v
        | _ -> failwith "Failed to materialize variable in calc expression"
    [<DebuggerStepThrough>]
    let vala = function
        | AnyTyped(TypedSNumber(v)) -> v
        | _ -> failwith "Failed to materialize variable in calc expression"
    [<DebuggerStepThrough>]
    let inc x = Plus (x, CalcAny(AnyTyped(snum 1.)))
    
    [<DebuggerStepThrough>]
    let inline (==>) sign bodyfn =
        let (Signature (_, l)) = sign
        Rule (sign, bodyfn l)

module ExecutionModule =
    let unifyParamsWithArguments parameters arguments =
        let prms = List.map2 (fun (Parameter(p)) (Argument(a)) ->
            match (p, a) with
            | (AnyVariable(v1), AnyVariable(v2)) -> Some p
            | (AnyVariable(v1), AnyTyped(v2)) -> Some a
            | (AnyTyped(v1), AnyVariable(v2)) -> Some p
            | (AnyTyped(v1), AnyTyped(v2)) when v1 = v2 -> Some a
            | _ -> None) parameters arguments
        if List.exists Option.isNone prms then
            None
        else
            Some <| List.map Option.get prms

    let rec unifyCalc changeVariable v =
        let changeCalcTermIfVariable =
            function
            | CalcInner c -> CalcInner(unifyCalc changeVariable c)
            | CalcAny(AnyVariable(v)) -> CalcAny(changeVariable v)
            | CalcAny(AnyTyped(v)) -> CalcAny(AnyTyped(v))
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
            | AnyTyped v -> expression
        | CallExpression (Goal(goalName, goalArgs)) -> 
            let newGoalArgs =
                List.map (fun (Argument(arg)) ->
                    match arg with
                    | AnyVariable(v) -> Argument(changeVariable v)
                    | AnyTyped(_) -> Argument(arg)) goalArgs
            CallExpression (Goal(goalName, newGoalArgs))
        | CalcExpr (v, c) ->
            match v with
            | AnyVariable(vv) -> CalcExpr(changeVariable vv, unifyCalc changeVariable c)
            | _ -> CalcExpr(v, unifyCalc changeVariable c)
        | EqExpr (e1, e2) ->
            match (e1, e2) with
            | (AnyVariable(v1), AnyVariable(v2)) -> EqExpr(changeVariable v1, changeVariable v2)
            | (AnyVariable(v1), AnyTyped(_)) -> EqExpr(changeVariable v1, e2)
            | (AnyTyped(_), AnyVariable(v2)) -> EqExpr(e1, changeVariable v2)
            | _ -> expression
        | GrExpr (e1, e2) ->
            match (e1, e2) with
            | (AnyVariable(v1), AnyVariable(v2)) -> GrExpr(changeVariable v1, changeVariable v2)
            | (AnyVariable(v1), AnyTyped(_)) -> GrExpr(changeVariable v1, e2)
            | (AnyTyped(_), AnyVariable(v2)) -> GrExpr(e1, changeVariable v2)
            | _ -> expression
        | LeExpr (e1, e2) ->
            match (e1, e2) with
            | (AnyVariable(v1), AnyVariable(v2)) -> LeExpr(changeVariable v1, changeVariable v2)
            | (AnyVariable(v1), AnyTyped(_)) -> LeExpr(changeVariable v1, e2)
            | (AnyTyped(_), AnyVariable(v2)) -> LeExpr(e1, changeVariable v2)
            | _ -> expression
        | _ -> failwith "unchecked something"

    // returns change variable functions according to execution branches
    let getChangedVariableFns initialExpression expression =
        let rec _getChangedVariableFn initialExpression expression (changedVariableFns: (Variable -> Any) list) =
            match (initialExpression, expression) with
            | (True, True) -> changedVariableFns
            | (False, False) -> changedVariableFns
            | (_, NotExecuted e) -> changedVariableFns
            | (NotExpression e1, NotExpression e2) -> _getChangedVariableFn e1 e2 changedVariableFns
            | (OrExpression(e1, e2), OrExpression(e3, e4)) ->
                let changedFn1 = _getChangedVariableFn e1 e3 changedVariableFns
                let changedFn2 = _getChangedVariableFn e2 e4 changedVariableFns
                changedFn1@changedFn2
            | (AndExpression(e1, e2), AndExpression(e3, e4)) ->
                let changedFn1 = _getChangedVariableFn e1 e3 changedVariableFns
                let changedFn2 = _getChangedVariableFn e2 e4 changedFn1
                changedFn2
            | (ResultExpression e1, ResultExpression e2) -> changedVariableFns |> List.map (fun fn -> fun v -> if AnyVariable(v) = e1 then e2 else fn v)
            | (CallExpression(Goal(name1, goalArgs1)), CallExpression(Goal(name2, goalArgs2))) when name1 = name2 ->
                 List.map (fun fn -> List.fold2 (fun fns a1 a2 -> fun v -> if AnyVariable(v) = a1 then a2 else fns v) fn (fromArgs goalArgs1) (fromArgs goalArgs2)) changedVariableFns
            | (CalcExpr(v1, _), CalcExpr(v2, _)) -> changedVariableFns |> List.map (fun fn -> fun v -> if AnyVariable(v) = v1 then v2 else fn v)
            | (EqExpr(v1, v2), EqExpr(v3, v4)) -> changedVariableFns |> List.map (fun fn -> fun v -> if AnyVariable(v) = v1 then v3 else if AnyVariable(v) = v2 then v4 else fn v)
            | (GrExpr(v1, v2), GrExpr(v3, v4)) -> changedVariableFns |> List.map (fun fn -> fun v -> if AnyVariable(v) = v1 then v3 else if AnyVariable(v) = v2 then v4 else fn v)
            | (LeExpr(v1, v2), LeExpr(v3, v4)) -> changedVariableFns |> List.map (fun fn -> fun v -> if AnyVariable(v) = v1 then v3 else if AnyVariable(v) = v2 then v4 else fn v)
            | _ -> failwithf "failed to getChangedVariableFn result. %O != %O" initialExpression expression
        _getChangedVariableFn initialExpression expression [(fun v -> AnyVariable(v))]
        
    let unifyExpressionByParams parameters arguments expression =
        let changeVariable (Parameter(p)) a =
            match (p, a) with
            | AnyVariable(v1), AnyVariable(v2) -> fun x -> if x = v2 then AnyVariable v1 else AnyVariable x
            | AnyVariable(v1), AnyTyped(v2) -> fun x -> if x = v1 then AnyTyped(v2) else AnyVariable x
            | AnyTyped(v1), AnyVariable(v2) -> fun x -> if x = v2 then AnyTyped(v1) else AnyVariable x
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

    let rec unifyBack arguments initialExpression expression =
        let unifyWithArgs args v1 v2 = args |> List.map (fun (a) -> if a = v1 then v2 else a)

        match (initialExpression, expression) with
        | (True, True) -> arguments
        | (False, False) -> []
        | (_, NotExecuted e) -> arguments
        | (NotExpression e1, NotExpression e2) -> unifyBack arguments e1 e2
        | (OrExpression(e1, e2), OrExpression(e3, e4)) -> unifyBack (unifyBack arguments e1 e3) e2 e4
        | (AndExpression(e1, e2), AndExpression(e3, e4)) -> unifyBack (unifyBack arguments e1 e3) e2 e4
        | (ResultExpression e1, ResultExpression e2) -> arguments |> List.map (fun a -> if a = e1 then e2 else a)
        | (CallExpression(Goal(name1, goalArgs1)), CallExpression(Goal(name2, goalArgs2))) when name1 = name2 ->
            List.fold2 (fun args (Argument(arg1)) (Argument(arg2)) -> unifyWithArgs args arg1 arg2) arguments goalArgs1 goalArgs2
        | (CalcExpr(v1, _), CalcExpr(v2, _)) -> unifyWithArgs arguments v1 v2
        | (EqExpr(v1, v2), EqExpr(v3, v4)) -> unifyWithArgs (unifyWithArgs arguments v1 v3) v2 v4
        | (GrExpr(v1, v2), GrExpr(v3, v4)) -> unifyWithArgs (unifyWithArgs arguments v1 v3) v2 v4
        | (LeExpr(v1, v2), LeExpr(v3, v4)) -> unifyWithArgs (unifyWithArgs arguments v1 v3) v2 v4
        | _ -> failwithf "failed to unify result. %O != %O" initialExpression expression

    // TODO: maybe we should unify each time we execute expression?
    let rec executeExpression (expr: Expression) executeCustom changeVariableFn =
        let changeAny =
            function
            | AnyVariable(v) -> changeVariableFn v
            | AnyTyped(v) -> AnyTyped(v)

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
        | CallExpression (Goal(goalSign, goalArgs)) ->
            executeCustom (Goal(goalSign, goalArgs))
            |> List.map (fun resExpr -> CallExpression(Goal(goalSign, resExpr |> toArgs)))
        | CalcExpr (v, c) ->
            let v = changeAny v
            let c = unifyCalc changeVariableFn c
            match v with
            | AnyVariable(vv) -> [CalcExpr(AnyTyped(TypedSNumber(executeCalc c)), c)]
            | AnyTyped(TypedSNumber(vv)) as ww when vv = (executeCalc c) -> [CalcExpr(AnyTyped(TypedSNumber(vv)), c)]
            | _ -> []
        | EqExpr (e1, e2) ->
            let e1 = changeAny e1
            let e2 = changeAny e2
            match (e1, e2) with
            | (AnyVariable(v1), AnyVariable(v2)) -> [EqExpr(e2, e2)]
            | (AnyVariable(v1), AnyTyped(v2)) -> [EqExpr(e2, e2)]
            | (AnyTyped(v1), AnyVariable(v2)) -> [EqExpr(e1, e1)]
            | (AnyTyped(v1), AnyTyped(v2)) when v1 = v2 -> [EqExpr(e2, e2)]
            | _ -> []
        | GrExpr (e1, e2) ->
            let e1 = changeAny e1
            let e2 = changeAny e2
            match (e1, e2) with
            | (AnyVariable(v1), AnyVariable(v2)) -> [GrExpr(e1, e2)]
            | (AnyVariable(v1), AnyTyped(v2)) -> [GrExpr(e1, e2)]
            | (AnyTyped(v1), AnyVariable(v2)) -> [GrExpr(e1, e2)]
            | (AnyTyped(v1), AnyTyped(v2)) when v1 > v2 -> [GrExpr(e1, e2)]
            | _ -> []
        | LeExpr (e1, e2) ->
            let e1 = changeAny e1
            let e2 = changeAny e2
            match (e1, e2) with
            | (AnyVariable(v1), AnyVariable(v2)) -> [LeExpr(e1, e2)]
            | (AnyVariable(v1), AnyTyped(v2)) -> [LeExpr(e1, e2)]
            | (AnyTyped(v1), AnyVariable(v2)) -> [LeExpr(e1, e1)]
            | (AnyTyped(v1), AnyTyped(v2)) when v1 < v2 -> [LeExpr(e1, e2)]
            | _ -> []
        | _ -> []

    // Idea is:
    // Expression is unified with arguments by parameters
    // Expression executes and all variables are resolved
    // Expression tree should be mostly unchanged
    // All changed variables can be caught afterwards
    let execute (Goal(name, arguments)) rule executeCustom =
        match unifyRule rule arguments with
        | Some (Rule(Signature(ruleName, unifiedRuleArgs), expr)) -> 
            if name = ruleName then
                let changeVar = List.fold2 (fun acc (Parameter(p)) (Argument(a)) -> fun v -> if AnyVariable(v) = p then a else acc v) (fun v -> AnyVariable(v)) unifiedRuleArgs arguments

                executeExpression expr executeCustom changeVar
                |> List.map (unifyBack (fromParams unifiedRuleArgs) expr) 
            else
                []
        | None -> []

    let checkApply (Goal(name, arguments)) (Rule(Signature(ruleName, ruleParams), _)) =
        name = ruleName && Option.isSome(unifyParamsWithArguments ruleParams arguments)

    let rec checkGoal goal knowledgeBase =
        knowledgeBase
        |> List.filter (checkApply goal)
        |> List.collect (fun r ->
            execute goal r (fun custom -> checkGoal custom knowledgeBase)
        )