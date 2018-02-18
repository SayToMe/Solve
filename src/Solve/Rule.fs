namespace Solve

open System.Diagnostics

open TermTypes

module Rule =
    type Argument = Argument of Term

    type Parameter = Parameter of Term

    type Signature = Signature of string * Parameter list
        with
        member self.AsString =
            let (Signature(name, parameters)) = self
            sprintf "%s/%d" name parameters.Length
        override self.ToString() = self.AsString
    type GoalSignature = GoalSignature of string * Argument list
        with
        member self.AsString =
            let (GoalSignature(name, parameters)) = self
            sprintf "%s/%d" name parameters.Length
        override self.ToString() = self.AsString

    type Calc =
        | Value of Term
        | Plus of Calc * Calc
        | Subsctruct of Calc * Calc
        | Invert of Calc
        | Multiply of Calc * Calc
        | Division of Calc * Calc
        | Sqrt of Calc
        | Log of Calc * Calc

    type Expression =
        | True
        | False
        | Cut
        | NotExecuted of Expression
        | NotExpression of Expression
        | OrExpression of Expression * Expression
        | AndExpression of Expression * Expression
        | ResultExpression of Term
        | CallExpression of GoalSignature
        | CalcExpr of Term * Calc
        | EqExpr of Term * Term
        | GrExpr of Term * Term
        | LeExpr of Term * Term
    and Rule = Rule of Signature * Expression
    and Goal = Goal of Expression

    type Result = Term list list

    module Transformers =
        [<DebuggerStepThrough>]
        let resp = function
            | Parameter(VariableTerm v) -> ResultExpression (VariableTerm v)
            | Parameter(TypedTerm v) -> ResultExpression (TypedTerm v)
            | Parameter(StructureTerm(v)) -> ResultExpression(StructureTerm(v))
            | Parameter(ListTerm(v)) -> ResultExpression(ListTerm(v))

        [<DebuggerStepThrough>]    
        let fromArgs = List.map (fun (Argument(a)) -> a)
        [<DebuggerStepThrough>]
        let toArgs = List.map Argument

        [<DebuggerStepThrough>]
        let fromParams = List.map (fun (Parameter(a)) -> a)
        [<DebuggerStepThrough>]
        let toParams = List.map Parameter

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