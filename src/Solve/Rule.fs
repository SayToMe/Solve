﻿namespace Solve

open System.Diagnostics

open TermTypes
open TermTypes.Transformers

module Rule =
    type Argument = Argument of Term

    type Parameter = Parameter of Term

    type Signature = Signature of string * Parameter list
    type Goal = Goal of Structure

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
        and CalcTerm = CalcAny of Term | CalcInner of Calc

    type Expression =
        | True
        | False
        | NotExecuted of Expression
        | NotExpression of Expression
        | OrExpression of Expression * Expression
        | AndExpression of Expression * Expression
        | ResultExpression of Term
        | CallExpression of Goal
        | CalcExpr of Term * Calc
        | EqExpr of Term * Term
        | GrExpr of Term * Term
        | LeExpr of Term * Term
    and Rule = Rule of Signature * Expression

    type Result = Term list list

    module Transformers =
        [<DebuggerStepThrough>]
        let resp = function
            | Parameter(VariableTerm v) -> ResultExpression (VariableTerm v)
            | Parameter(TypedTerm v) -> ResultExpression (TypedTerm v)
            | Parameter(StructureTerm(v)) -> ResultExpression(StructureTerm(v))

        [<DebuggerStepThrough>]
        let signature (name: string) (prms: Term list) =
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
            format (format (fun (a: Term) -> a.AsString)) result

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
            | Parameter(TypedTerm(TypedNumberTerm(v))) -> v
            | _ -> failwith "Failed to materialize variable in calc expression"
        [<DebuggerStepThrough>]
        let vala = function
            | TypedTerm(TypedNumberTerm(v)) -> v
            | _ -> failwith "Failed to materialize variable in calc expression"
    
        [<DebuggerStepThrough>]
        let inline (==>) sign bodyfn =
            let (Signature (_, l)) = sign
            Rule (sign, bodyfn l)