namespace Solve

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
        type Variable = Variable of string | WildVariable

type Any = AnyVariable of Variable | AnyTyped of Typed

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
    // Used as false or not executed cut
    | NotExecuted of Expression
    | NotExpression of Expression
    | OrExpression of Expression * Expression
    | AndExpression of Expression * Expression
    | ResultExpression of Any
    | CallExpression of (Goal * Rule)
    | CalcExpr of Any * Calc
    | EqExpr of Any * Any
    | GrExpr of Any * Any
    | LeExpr of Any * Any
and Rule = Rule of Signature * Expression

[<AutoOpen>]
module MainModule = 
    let variable (name: string) = AnyVariable (Variable name)
    let resv v = ResultExpression (AnyVariable v)
    let res t = ResultExpression (AnyTyped t)
    let resa a = ResultExpression a
    let resp = function
        | Parameter(AnyVariable v) -> resv v
        | Parameter(AnyTyped v) -> res v

    let signature (name: string) (prms: Any list) =
        Signature (name, List.map Parameter prms)
        
    let fromArgs = List.map (fun (Argument(a)) -> a)
    let toArgs = List.map (fun a -> Argument(a))

    let fromParams = List.map (fun (Parameter(a)) -> a)
    let toParams = List.map (fun a -> Parameter(a))

    let sbool v = TypedSBool <| SBool v
    let strue = sbool true
    let sfalse = sbool false

    let snum v = TypedSNumber <| SNumber v
    let snum1 = snum 1.

    let schar v = TypedSChar <| SChar v

    let (=>) sign body = Rule (sign, body)
    let (/=>) name variables = signature name variables
    let (/|) expr1 expr2 = OrExpression (expr1, expr2)
    let (/&) expr1 expr2 = AndExpression (expr1, expr2)

    let (/=) e1 e2 = EqExpr (e1, e2)
    let (/>) e1 e2 = GrExpr (e1, e2)
    let (/<) e1 e2 = LeExpr (e1, e2)

    let valp = function
        | Parameter(AnyTyped(TypedSNumber(v))) -> v
        | _ -> failwith "Failed to materialize variable in calc expression"
    let vala = function
        | AnyTyped(TypedSNumber(v)) -> v
        | _ -> failwith "Failed to materialize variable in calc expression"
    let inc x = Plus (x, CalcAny(AnyTyped(snum 1.)))
    
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

    let rec unifyExpression expression changeVariable =
                match expression with
                | NotExpression e -> NotExpression (unifyExpression e changeVariable)
                | OrExpression (e1, e2) -> OrExpression(unifyExpression e1 changeVariable, unifyExpression e2 changeVariable)
                | AndExpression (e1, e2) -> AndExpression(unifyExpression e1 changeVariable, unifyExpression e2 changeVariable)
                | ResultExpression e ->
                    match e with
                    | AnyVariable v -> ResultExpression (changeVariable v)
                    | AnyTyped v -> expression
                //| CallExpression (Rule(Signature(n, prms1), expr1), l) -> 
                //    expression
                    //CallExpression (Rule(Signature(n, prms1), expr1), l) (prms1 |> List.map (fun (Parameter(p)) -> p)) expr1
                | CalcExpr (v, c) ->
                    let rec unifyCalc =
                        let changeCalcTermIfVariable =
                            function
                            | CalcInner c -> CalcInner(unifyCalc c)
                            | CalcAny v ->
                                match v with
                                | AnyVariable v -> CalcAny(changeVariable v)
                                | AnyTyped _ -> CalcAny v
                        function
                        | Plus (v1, v2) -> Plus(changeCalcTermIfVariable v1, changeCalcTermIfVariable v2)
                        | Subsctruct (v1, v2) -> Subsctruct(changeCalcTermIfVariable v1, changeCalcTermIfVariable v2)
                        | Multiply (v1, v2) -> Multiply(changeCalcTermIfVariable v1, changeCalcTermIfVariable v2)
                        | Division (v1, v2) -> Division(changeCalcTermIfVariable v1, changeCalcTermIfVariable v2)
                        | Invert (v1) -> Invert(changeCalcTermIfVariable v1)
                        | Sqrt (v1) -> Sqrt(changeCalcTermIfVariable v1)
                        | Log (v1, n) -> Log(changeCalcTermIfVariable v1, changeCalcTermIfVariable n)
                    match v with
                    | AnyVariable(vv) -> CalcExpr(changeVariable vv, unifyCalc c)
                    | _ -> expression
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
        | (_, NotExecuted e) -> arguments
        | (NotExpression e1, NotExpression e2) -> unifyBack arguments e1 e2
        | (OrExpression(e1, e2), OrExpression(e3, e4)) -> unifyBack (unifyBack arguments e1 e3) e2 e4
        | (AndExpression(e1, e2), AndExpression(e3, e4)) -> unifyBack (unifyBack arguments e1 e3) e2 e4
        | (ResultExpression e1, ResultExpression e2) -> arguments |> List.map (fun a -> if a = e1 then e2 else a)
        //| CallExpression (Rule(Signature(n, prms1), expr1), l) ->
        //    executeExpression prms1 expr1
        //    |> Option.bind (fun resExpr -> Some(CallExpression(Rule(Signature(n, prms1), resExpr), l)))
        | (CalcExpr(v1, _), CalcExpr(v2, _)) -> unifyWithArgs arguments v1 v2
        | (EqExpr(v1, v2), EqExpr(v3, v4)) -> unifyWithArgs (unifyWithArgs arguments v1 v3) v2 v4
        | (GrExpr(v1, v2), GrExpr(v3, v4)) -> unifyWithArgs (unifyWithArgs arguments v1 v3) v2 v4
        | (LeExpr(v1, v2), LeExpr(v3, v4)) -> unifyWithArgs (unifyWithArgs arguments v1 v3) v2 v4
        | _ -> failwithf "failed to unify result. %O != %O" initialExpression expression

    // TODO: maybe we should unify each time we execute expression?
    let rec executeExpression (parameters: Argument list) (expr: Expression) =
            match expr with
            | NotExpression e -> List.map (NotExpression) (executeExpression parameters e)
            | OrExpression (e1, e2) ->
                let first = executeExpression parameters e1 |> List.map (fun v -> OrExpression(v, NotExecuted e2))
                let second = (executeExpression parameters e2 |> List.map (fun x -> OrExpression(NotExecuted e1, x)))
                first@second
            | AndExpression (e1, e2) ->
                executeExpression parameters e1
                |> List.collect (fun e1_ ->
                    let newParameters = unifyBack (fromArgs parameters) e1 e1_ |> toArgs

                    match unifyExpressionByParams (parameters |> fromArgs |> toParams) newParameters e2 with
                    //| Some(e2_, newArgs) -> executeExpression newParameters e2_ |> List.map(fun e2__ -> AndExpression(e1_, e2__))
                    | Some(e2_, newArgs) -> executeExpression (toArgs newArgs) e2_ |> List.map(fun e2__ -> AndExpression(e1_, e2__))
                    | None -> []
                )
            | ResultExpression e -> [ResultExpression e]
            //| CallExpression (Rule(Signature(n, prms1), expr1), l) ->
            //    executeExpression prms1 expr1
            //    |> Option.bind (fun resExpr -> Some(CallExpression(Rule(Signature(n, prms1), resExpr), l)))
            | CalcExpr (v, c) ->
                match v with
                | AnyVariable(vv) -> [CalcExpr(AnyTyped(TypedSNumber(executeCalc c)), c)]
                | AnyTyped(TypedSNumber(vv)) as ww when vv = (executeCalc c) -> [CalcExpr(AnyTyped(TypedSNumber(vv)), c)]
                | _ -> []
            | EqExpr (e1, e2) ->
                match (e1, e2) with
                | (AnyVariable(v1), AnyVariable(v2)) -> [EqExpr(e2, e2)]
                | (AnyVariable(v1), AnyTyped(v2)) -> [EqExpr(e2, e2)]
                | (AnyTyped(v1), AnyVariable(v2)) -> [EqExpr(e1, e1)]
                | (AnyTyped(v1), AnyTyped(v2)) when v1 = v2 -> [EqExpr(e2, e2)]
                | _ -> []
            | GrExpr (e1, e2) ->
                match (e1, e2) with
                | (AnyVariable(v1), AnyVariable(v2)) -> [GrExpr(e2, e2)]
                | (AnyVariable(v1), AnyTyped(v2)) -> [GrExpr(e2, e2)]
                | (AnyTyped(v1), AnyVariable(v2)) -> [GrExpr(e1, e1)]
                | (AnyTyped(v1), AnyTyped(v2)) when v1 > v2 -> [GrExpr(e2, e2)]
                | _ -> []
            | LeExpr (e1, e2) ->
                match (e1, e2) with
                | (AnyVariable(v1), AnyVariable(v2)) -> [LeExpr(e2, e2)]
                | (AnyVariable(v1), AnyTyped(v2)) -> [LeExpr(e2, e2)]
                | (AnyTyped(v1), AnyVariable(v2)) -> [LeExpr(e1, e1)]
                | (AnyTyped(v1), AnyTyped(v2)) when v1 < v2 -> [LeExpr(e2, e2)]
                | _ -> []
            | _ -> []
            
    // Idea is:
    // Expression is unified with arguments by parameters
    // Expression executes and all variables are resolved
    // Expression tree should be mostly unchanged
    // All changed variables can be caught afterwards
    let execute goal rule = 
        let (Goal(name, arguments)) = goal
        match unifyRule rule arguments with
        | Some (Rule(Signature(ruleName, unifiedRuleArgs), expr)) -> 
            if name = ruleName then
                executeExpression (fromParams unifiedRuleArgs |> toArgs) expr
                |> List.map (unifyBack (fromParams unifiedRuleArgs) expr)
            else
                []
        | None -> []