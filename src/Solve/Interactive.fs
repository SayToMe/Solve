namespace Solve

open Microsoft.FSharp.Text.Lexing
open Rule
open Rule.Transformers
open TermTypes

type InteractiveResult =
    | RuleInfo of Rule
    | SolveResult of string seq
    | NoResult

type Interactive() =
    let mutable _knowledgebase = []

    member self.NewInput text =
        let lexbuf = LexBuffer<char>.FromString text

        match PrologParser.start PrologLexer.read lexbuf with
        | Some (PrologParser.RuleParseResult(rule)) -> 
            _knowledgebase <- _knowledgebase@[rule]
            RuleInfo(rule)
        | Some (PrologParser.CallParseResult goal) -> 
            let solved = Solve.solve goal _knowledgebase
            let mapped =
                solved
                |> Seq.map (fun result ->
                         let (Solve.Rule.Goal(Solve.TermTypes.Structure(_, args))) = goal
                         let variableArgs = 
                              args
                              |> List.mapi (fun i arg -> (arg, i))
                              |> List.filter (fun (arg, _) ->
                                                  match arg with
                                                  | (VariableTerm(_)) -> true
                                                  | _ -> false
                                             )
                              |> List.map (fun (arg, i) -> match arg with | (VariableTerm(Variable(var))) -> (var, i) | _ -> failwith "")
                              |> List.distinctBy (fun (v, _) -> v)
                         let getVariableResult (_, i) =
                              result.[i]
                         variableArgs
                         |> List.map (fun v -> v, getVariableResult v)
                         |> List.map (fun ((var, _), res) -> var + " = " + (string res))
                         |> List.reduce (fun acc c -> acc + ", " + c)
                )
            SolveResult mapped
        | None -> NoResult