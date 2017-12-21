﻿open Solve

open System

type Mode =
    | Insert
    | Query
    
let deletePrevConsoleLine() =
    if Console.CursorTop > 0 then
        Console.Write(new string(' ', Console.WindowWidth))
        Console.SetCursorPosition(0, Console.CursorTop - 1)
        
let readInput mode =
    match mode with
    | Insert -> printf "> "
    | Query -> printf "?- "

    let input = Console.ReadLine()
    match mode with
    | Insert -> input
    | Query -> "?- " + input

[<EntryPoint>]
let main argv = 
    let interactive = Solve.Interactive()
    
    printfn "Choose mode by typing: 'insert' (>) or 'query' (?-)."

    let mutable mode = Insert
    let mutable input = readInput mode

    while input <> "exit" do
        try
            match input with
            | "> exit"
            | "?- exit"
            | "exit"

            | "> insert"
            | "?- insert"
            | "insert" -> mode <- Insert
            | "> query"
            | "?- query"
            | "query" -> mode <- Query
            | _ ->
                match interactive.NewInput input with
                | RuleInfo(r) -> printfn "%A" r
                | SolveResult(r) ->
                    let rec proc seq checkKey =
                        let checkBackTrack() =
                            let rk = Console.ReadKey()
                            rk.Key = ConsoleKey.Enter || rk.KeyChar = ';'

                        let backtrack = not checkKey || checkBackTrack()
                        deletePrevConsoleLine()

                        if backtrack then
                            match Seq.tryHead seq with
                            | Some answ -> 
                                printfn "%A" (answ)
                                proc (Seq.tail seq) true
                            | None -> printfn "fail"
                    proc r false
                    printfn ""
                | _ -> ()
        with
        | _ as e -> printfn "Failed. %A" e.Message

        input <- readInput mode
        
    0
