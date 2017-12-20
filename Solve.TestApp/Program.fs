// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.

open Solve

open TermTypes
open TermTypes.Transformers

open Rule
open Rule.Transformers

open System

[<EntryPoint>]
let main argv = 
    let i = Solve.Interactive()

    let mutable input = Console.ReadLine()
    while input <> "exit" do
        try
            match i.NewInput input with
            | RuleInfo(r) -> printfn "%A" r
            | SolveResult(r) ->
                let rec proc seq checkKey =
                    let checkBackTrack() =
                        let rk = Console.ReadKey()
                        let key = rk.Key
                        key = ConsoleKey.Enter || rk.KeyChar = ';'

                    if not checkKey || checkBackTrack() then
                        match Seq.tryHead seq with
                        | Some answ -> 
                            printfn "%A" (answ)
                            proc (Seq.tail seq) true
                        | None -> printfn "fail"
                proc r false
                printfn ""
            | _ -> ()
        with
        | _ as e -> printfn "Failed to parse previous input"

        input <- System.Console.ReadLine()

    0 // return an integer exit code
