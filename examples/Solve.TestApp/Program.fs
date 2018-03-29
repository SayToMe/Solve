open Solve
open Solve.Parse

open System
open System.Text.RegularExpressions

// ParseRegex parses a regular expression and returns a list of the strings that match each group in
// the regular expression.
// List.tail is called to eliminate the first element in the list, which is the full matched expression,
// since only the matches for each group are wanted.
let (|ParseRegex|_|) regex str =
   let m = Regex(regex).Match(str)
   if m.Success
   then Some (List.tail [ for x in m.Groups -> x.Value ])
   else None

type Mode =
    | Insert
    | Query
    | Exit

type BackTrackMode =
    | NoBackTrack
    | SingleBackTrack
    | AlwaysBackTrack

let deletePrevConsoleLine() =
    if Console.CursorTop > 0 then
        Console.Write(new string(' ', Console.WindowWidth))
        Console.SetCursorPosition(0, Console.CursorTop - 1)
        
let prepareInput mode =
    match mode with
    | Insert -> printf ":-"
    | Query -> printf "?-"
    | Exit -> ()

    let input = Console.ReadLine()
    match mode with
    | Insert -> ":-" + input
    | Query -> "?-" + input
    | Exit -> ""

[<EntryPoint>]
let main argv = 
    let interactive = Solve.Parse.Interactive()
    
    printfn "Choose mode by typing: 'insert' (:-) or 'query' (?-)."

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

    let rec cycle mode =
        match mode with
        | Exit -> ()
        | Insert
        | Query ->
            try
                let input = prepareInput mode
                match input with
                | ParseRegex "^[:?]-\s*exit\s*$" _ ->
                    cycle Exit
                | ParseRegex "^[:?]-\s*insert\s*$" _ ->
                    cycle Insert
                | ParseRegex "^[:?]-\s*query\s*$" _ ->
                    cycle Query
                | _ ->
                    match interactive.NewInput input with
                    | RuleInfo(Rule.Rule(sign, _)) as r -> 
                        printfn "Insertion succeed: %O." sign
                        printfn "Rule: %A" r

                        cycle mode
                    | SolveResult(results) ->
                        let getBackTrackMode() =
                            let rk = Console.ReadKey()
                            deletePrevConsoleLine()
                            match rk.Key with
                            | ConsoleKey.Escape -> NoBackTrack
                            | ConsoleKey.Spacebar
                            | ConsoleKey.Enter -> SingleBackTrack
                            | ConsoleKey.A -> AlwaysBackTrack
                            | _ ->
                                match rk.KeyChar with
                                | ';' -> SingleBackTrack
                                | '.' -> NoBackTrack
                                | _ -> SingleBackTrack
                        results
                        |> Seq.unfold (fun st ->
                            match Seq.tryHead st with
                            | Some answ ->
                                let showAnswer answ = if answ = "" then printfn "true" else printfn "%A" answ

                                showAnswer answ

                                match getBackTrackMode() with
                                | SingleBackTrack -> Some (answ, Seq.tail st)
                                | AlwaysBackTrack -> 
                                    Seq.iter showAnswer (Seq.tail st)
                                    printfn "false"
                                    None
                                | NoBackTrack -> None
                            | _ ->
                                printfn "false"
                                None
                        )
                        |> Seq.iter ignore

                        cycle mode
                    | Error e ->
                        printfn "Error. %A" e
                        cycle mode
                    | NoResult -> cycle mode
            with
            | _ as e ->
                printfn "Failure. %A" e.Message
                cycle mode

    cycle Insert
    0
