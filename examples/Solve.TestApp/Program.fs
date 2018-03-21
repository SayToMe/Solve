open Solve
open Solve.Parse

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
    | Insert -> printf ":-"
    | Query -> printf "?-"

    let input = Console.ReadLine()
    match mode with
    | Insert -> ":-" + input
    | Query -> "?-" + input

[<EntryPoint>]
let main argv = 
    let interactive = Solve.Parse.Interactive()
    
    printfn "Choose mode by typing: 'insert' (:-) or 'query' (?-)."

    let mutable mode = Insert
    let mutable input = readInput mode

    // Factorial example
    // factorial(1,1).
    // factorial(X,Y) :- X > 1, X1 is X - 1, factorial(X1, Y1), Y is X * Y1.

    // Parent example
    // >>> person(name)
    // person(masha).
    // person(misha).
    // person(alex).
    // person(sova).
    // >>> parent(Parent, Child)
    // parent(alex, masha).
    // parent(alex, sova).
    // parent(masha, misha).
    // >>> grandparent(GrandParent, GrandChild)
    // grandparent(GP, GC) :- parent(GP, P), parent(P, GC).

    while input <> "exit" do
        try
            match input with
            | ":- exit"
            | "?- exit"
            | "exit"

            | ":- insert"
            | "?- insert"
            | "insert" -> mode <- Insert
            | ":- query"
            | "?- query"
            | "query" -> mode <- Query
            | _ ->
                match interactive.NewInput input with
                | RuleInfo(Rule.Rule(sign, _)) as r -> 
                    printfn "Insertion succeed: %O." sign
                    printfn "Rule: %A" r
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
