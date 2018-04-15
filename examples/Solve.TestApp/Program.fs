open Solve
open Solve.PrologParser

open System
open System.Text.RegularExpressions

open Solve.Terminal

// ParseRegex parses a regular expression and returns a list of the strings that match each group in
// the regular expression.
// List.tail is called to eliminate the first element in the list, which is the full matched expression,
// since only the matches for each group are wanted.
let (|ParseRegex|_|) regex str =
   let m = Regex(regex).Match(str)
   if m.Success
   then Some (List.tail [ for x in m.Groups -> x.Value ])
   else None

let deletePrevConsoleLine() =
    if Console.CursorTop > 0 then
        Console.Write(new string(' ', Console.WindowWidth))
        Console.SetCursorPosition(0, Console.CursorTop - 1)

type ConsoleTerminal() =
    let kb: IKnowledgebaseWrapper = MutableKnowledgebase([]) :> IKnowledgebaseWrapper

    interface ITerminal with
        member __.Solve goal = kb.Solve goal
        member __.Insert rule = kb.AddRule rule
        member __.Log logMessage =
            match logMessage with
            | ModeLog mode -> printf "%s" mode.AsString
            | InfoLog info -> printfn "%s" info
            | SuccessInsertionLog(name, arity) -> printfn "Success insertion of %s/%i" name arity
            | ResultLog res -> printfn "%s" res
            | ErrorLog error -> printfn "Error: %s" error
        member __.ReadInput() = Console.ReadLine()
        member __.ReadKey() = Console.ReadKey()

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

[<EntryPoint>]
let main argv =
    let terminal = ConsoleTerminal()

    Welcome
    |> Seq.unfold (
        function
        | End -> None
        | _ as mode -> Some <| (0, run terminal mode)
    )
    |> Seq.iter ignore

    Console.ReadKey() |> ignore
    0
