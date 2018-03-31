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
            | Parameter(VariableTerm variableTerm) -> ResultExpression (VariableTerm variableTerm)
            | Parameter(TypedTerm typedTerm) -> ResultExpression (TypedTerm typedTerm)
            | Parameter(StructureTerm(structureTerm)) -> ResultExpression(StructureTerm(structureTerm))
            | Parameter(ListTerm(listTerm)) -> ResultExpression(ListTerm(listTerm))

        [<DebuggerStepThrough>]    
        let fromArgs = List.map (fun (Argument(term)) -> term)
        [<DebuggerStepThrough>]
        let toArgs = List.map Argument

        [<DebuggerStepThrough>]
        let fromParams = List.map (fun (Parameter(term)) -> term)
        [<DebuggerStepThrough>]
        let toParams = List.map Parameter

        [<DebuggerStepThrough>]
        let formatResult (result: Result) =
            let format formatFn =
                function
                | [] -> "[]"
                | [head] -> "[" + formatFn head + "]"
                | list -> "[" + (List.fold (fun acc current -> if acc = "" then formatFn current else acc + ", " + formatFn current) "" list) + "]"
            format (format (fun (term: Term) -> term.AsString)) result

    module Builder =
        [<DebuggerStepThrough>]
        let (=>) sign body = Rule (sign, body)
        [<DebuggerStepThrough>]
        let (/=>) name variables = Signature(name, variables)
        [<DebuggerStepThrough>]
        let (/|) leftExpr rightExpr = OrExpression (leftExpr, rightExpr)
        [<DebuggerStepThrough>]
        let (/&) leftExpr rightExpr = AndExpression (leftExpr, rightExpr)

        [<DebuggerStepThrough>]
        let (/=) leftTerm rightTerm = EqExpr (leftTerm, rightTerm)
        [<DebuggerStepThrough>]
        let (/>) leftTerm rightTerm = GrExpr (leftTerm, rightTerm)
        [<DebuggerStepThrough>]
        let (/<) leftTerm rightTerm = LeExpr (leftTerm, rightTerm)
        
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