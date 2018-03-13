namespace Solve

open Rule
open Rule.Transformers
open TermTypes
open FParsec

open Solve.Parse

type InteractiveResult =
    | RuleInfo of Rule
    | SolveResult of string seq
    | Error of string
    | NoResult

type Interactive() =
    let mutable _knowledgebase = []

    member self.NewInput (text: string) =
        match parsePlString text with
        | RuleParseResult(rule) -> 
            _knowledgebase <- _knowledgebase@[rule]
            RuleInfo(rule)
        | CallParseResult goal ->
            let solved = Solve.solve goal _knowledgebase

            solved
            |> Seq.map (fun result ->
                result
                |> List.fold (fun acc (v, t) ->
                    let str = (VariableTerm(v).AsString + " = " + t.AsString)
                    if String.length acc = 0 then
                        str
                    else
                        acc + ", " + str
                ) ""
            )
            |> SolveResult
        | ParseError(err) -> Error err