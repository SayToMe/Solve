namespace Solve

open System.Diagnostics

open Types
open Types.Transformers

module Rule =
    type Argument = Argument of Any

    type Parameter = Parameter of Any

    type Signature = Signature of string * Parameter list
    type Goal = Goal of Struct

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

    module Transformers =
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
            | Parameter(AnyStruct(v)) -> ResultExpression(AnyStruct(v))

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
        let formatResult (result: Result) =
            let format fn =
                function
                | [] -> "[]"
                | [h] -> "[" + fn h + "]"
                | list -> "[" + (List.fold (fun acc n -> if acc = "" then fn n else acc + ", " + fn n) "" list) + "]"
            format (format (fun (a: Any) -> a.AsString)) result

    module Builder =
        [<DebuggerStepThrough>]
        let (=>) sign body = Rule (sign, body)
        [<DebuggerStepThrough>]
        let (/=>) name variables = Signature(name, variables)
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