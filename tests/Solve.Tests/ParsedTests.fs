module Solve.ParsedTests

open NUnit.Framework
open System.Diagnostics

open Solve

open TermTypes
open TermTypes.Transformers

open Rule
open Rule.Transformers
open VariableUnify
open ExpressionUnify

open System
open Solve.Terminal

let (|>>) terminal input =
    consumeInput terminal TerminalMode.Insert input
    terminal

let (|?>) terminal input =
    consumeInput terminal TerminalMode.Query input
    terminal

type TestTerminal() as self =
    let kb: IKnowledgebaseWrapper = MutableKnowledgebase([]) :> IKnowledgebaseWrapper
    let mutable output: string list = []

    member __.Output = output

    member __.ResetOutput() = output <- []

    member __.GetResults res =
        let mutable tempOutput: string list = []
        showResult res (fun s -> tempOutput <- sprintf "%s" s :: tempOutput) (fun _ -> BackTrackMode.AlwaysBackTrack) 
        List.rev tempOutput

    interface ITerminal with
        member __.Solve goal = kb.Solve goal
        member __.Insert rule = kb.AddRule rule
        member __.Log logMessage =
            match logMessage with
            | ModeLog mode -> printf "%s" mode.AsString
            | InfoLog info -> printfn "%s" info
            | SuccessInsertionLog(name, arity) -> printfn "Success insertion of %s/%i" name arity
            | ResultLog res ->
                output <- output @ self.GetResults res
            | ErrorLog error -> printfn "Error: %s" error
        member __.ReadInput() = failwith "ReadInput not implemented"
        member __.ReadKey() = failwith "ReadKey not implemented"

let checkOutput expected (terminal: TestTerminal) =
    let expected = Seq.toList expected
    Assert.AreEqual(terminal.Output, expected, sprintf "%O != %O" expected terminal.Output)

let expectedResult expected (terminal: TestTerminal) =
    let expected = expected |> convertSolveResult |> terminal.GetResults
    let actual = terminal.Output
    Assert.AreEqual(actual, expected, sprintf "%O != %O" expected actual)
    terminal.ResetOutput()
    terminal

[<TestFixture>]
module ParsedFactorialTests =
    [<Test>]
    let ``Check facts test``() =
        TestTerminal()
        |>> "fact(1, 1)."
        |>> "fact(X, R):- X > 1, X1 is X - 1, fact(X1, R1), R is R1 * X."
        |?> "fact(1, X)."
        |> expectedResult [[(Variable "X", num 1.)]]
        |?> "fact(2, X)."
        |> expectedResult [[(Variable "X", num 2.)]]
        |?> "fact(3, X)."
        |> expectedResult [[(Variable "X", num 6.)]]
        |?> "fact(5, 120)."
        |> expectedResult [[]]
        |> ignore
        
[<TestFixture>]
module ParsedFactTests =
    [<Test>]
    let ``Check facts test``() =
        TestTerminal()
        |>> "test(1)."
        |>> "test(2)."
        |?> "test(X)."
        |> expectedResult [[(Variable "X", num 1.)]; [(Variable "X", num 2.)]]
        |> ignore
        
[<TestFixture>]
module ParsedListTests =
    let insertHeadRule terminal =
        terminal
        |>> "head(H, L) :- [H | R] = L"
        
    let insertTailRule terminal =
        terminal
        |>> "tail(T, L) :- [T1 | T] = L" // Could be used with wildcard variable
        
    let insertMemberRule terminal =
        terminal
        |>> "member(E, L) :- head(E, L)."
        |>> "member(E, L) :- tail(T, L), member(E, T)."
        
    [<Test>]
    let ``Check head on empty list test``() =
        TestTerminal()
        |> insertHeadRule
        |?> "head(X, [])."
        |> expectedResult []
        |> ignore
        
    [<Test>]
    let ``Check head on list test``() =
        TestTerminal()
        |> insertHeadRule
        |?> "head(X, [1, 2, 3])."
        |> expectedResult [[(Variable "X", num 1.)]]
        |> ignore
        
    [<Test>]
    let ``Check tail on empty list test``() =
        TestTerminal()
        |> insertTailRule
        |?> "tail(X, [])."
        |> expectedResult []
        |> ignore
        
    [<Test>]
    let ``Check tail on single element list test``() =
        TestTerminal()
        |> insertTailRule
        |?> "tail(X, [1])."
        |> expectedResult [[(Variable "X", numList [])]]
        |> ignore
        
    [<Test>]
    let ``Check tail on list test``() =
        TestTerminal()
        |> insertTailRule
        |?> "tail(X, [1, 2, 3])."
        |> expectedResult [[(Variable "X", numList [2.; 3.])]]
        |> ignore
        
    [<Test>]
    let ``Check member on empty list test``() =
        TestTerminal()
        |> insertHeadRule
        |> insertTailRule
        |> insertMemberRule
        |?> "member(X, [])."
        |> expectedResult []
        |> ignore
        
    [<Test>]
    let ``Check member on list test``() =
        TestTerminal()
        |> insertHeadRule
        |> insertTailRule
        |> insertMemberRule
        |?> "member(X, [1, 2])."
        |> expectedResult [[(Variable "X", num 1.)]; [(Variable "X", num 2.)]]
        |> ignore
        
    [<Test>]
    let ``Check member on first list test``() =
        TestTerminal()
        |> insertHeadRule
        |> insertTailRule
        |> insertMemberRule
        |?> "member(1, [1, 2])."
        |> expectedResult [[]]
        |> ignore
        
    [<Test>]
    let ``Check member on second list test``() =
        TestTerminal()
        |> insertHeadRule
        |> insertTailRule
        |> insertMemberRule
        |?> "member(2, [1, 2])."
        |> expectedResult [[]]
        |> ignore