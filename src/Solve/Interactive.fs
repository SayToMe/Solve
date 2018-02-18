namespace Solve

open Rule
open TermTypes

open Solve.Parse

type InteractiveResult =
    | RuleInfo of Rule
    | SolveResult of string seq
    | NoResult

type Interactive() =
    let mutable _knowledgebase = []

    member self.NewInput (text: string) =
        match parse text with
        | Some (PrologParser.RuleParseResult(rule)) -> 
            _knowledgebase <- _knowledgebase@[rule]
            RuleInfo(rule)
        | Some (PrologParser.CallParseResult goal) -> 
            Solve.solve goal _knowledgebase
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
        | None -> NoResult