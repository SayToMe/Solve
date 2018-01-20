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

    member self.NewInput text =
        match parse text with
        | Some (PrologParser.RuleParseResult(rule)) -> 
            _knowledgebase <- _knowledgebase@[rule]
            RuleInfo(rule)
        | Some (PrologParser.CallParseResult goal) -> 
            let solved = Solve.solve goal _knowledgebase
            let mapped =
                solved
                |> Seq.map (fun result ->
                         let (Solve.Rule.Goal(Solve.TermTypes.Structure(_, args))) = goal

                         let concatVarUnificationResult acc s =
                            if String.length s = 0 then acc elif String.length acc = 0 then s else acc + ", " + s

                         let rec findUnification t1 t2 =
                            match t1, t2 with
                            | VariableTerm(Variable(v)), (res: Term) -> v + " = " + (res.AsString)
                            | StructureTerm(Structure(_, sArgs1)), StructureTerm(Structure(_, sArgs2)) ->
                                (sArgs1, sArgs2)
                                ||> List.map2 (fun a1 a2 -> findUnification a1 a2)
                                |> List.fold concatVarUnificationResult ""
                            | ListTerm(l1), ListTerm(l2) ->
                                let rec procListVars l1 l2 =
                                    match l1, l2 with
                                    | VarListTerm(Variable(v)), (t: TypedListTerm) -> v + " = " + (t.AsString)
                                    | TypedListTerm(h1, t1), TypedListTerm(h2, t2) ->
                                        concatVarUnificationResult (findUnification h1 h2) (procListVars t1 t2)
                                    | _ -> ""
                                procListVars l1 l2
                            | _, _ -> ""

                         (args, result)
                         ||> List.map2 findUnification
                         |> List.fold concatVarUnificationResult ""
                )
            SolveResult mapped
        | None -> NoResult