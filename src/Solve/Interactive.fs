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
            _knowledgebase <- rule :: _knowledgebase
            RuleInfo(rule)
        | Some (PrologParser.CallParseResult goal) -> 
            let solved = Solve.solve goal _knowledgebase
            let mapped =
                Seq.map (fun m ->
                       let (Solve.Rule.Goal(Solve.TermTypes.Structure(_, args))) = goal
                       (args, m) ||> List.map2 (fun v1 v2 -> (string v1) + " = " + (string v2)) |> List.reduce (+)
                ) solved
            SolveResult mapped
        | None -> NoResult