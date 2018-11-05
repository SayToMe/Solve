module Solve.ParsedTests

open NUnit.Framework

open Solve

open TermTypes
open TermTypes.Transformers

open Solve.Terminal

let (|->) terminal input =
    try
        consumeInput terminal TerminalMode.Insert input
        terminal
    with
    | e -> Assert.Fail(sprintf "Exception while consuming input: %s" e.Message)
           terminal

let (|?>) terminal input =
    try
        consumeInput terminal TerminalMode.Query input
        terminal
    with
    | e -> Assert.Fail(sprintf "Exception while consuming input: %s" e.Message)
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
    try
        let expected = expected |> convertSolveResult |> terminal.GetResults
        let actual = terminal.Output
        Assert.AreEqual(actual, expected, sprintf "%O != %O" expected actual)
        terminal.ResetOutput()
        terminal
    with
        | e -> Assert.Fail(sprintf "Thrown exception %s" e.Message)
               terminal

[<TestFixture>]
module ParsedFactorialTests =
    let insertFactorialRule terminal =
        terminal
        |-> "factorial(1, 1)."
        |-> "factorial(X, R):- X > 1, X1 is X - 1, factorial(X1, R1), R is R1 * X."

    [<Test>]
    let ``Given `factorial` solve with factorial(1, X) should return [X = 1]``() =
        insertFactorialRule (TestTerminal())
        |?> "factorial(1, X)."
        |> expectedResult [[(Variable "X", num 1.)]]
        |> ignore

    [<Test>]
    let ``Given `factorial` solve with factorial(2, X) should return [X = 2]``() =
        insertFactorialRule (TestTerminal())
        |?> "factorial(2, X)."
        |> expectedResult [[(Variable "X", num 2.)]]
        |> ignore

    [<Test>]
    let ``Given `factorial` solve with factorial(3, X) should return [X = 6]``() =
        insertFactorialRule (TestTerminal())
        |?> "factorial(3, X)."
        |> expectedResult [[(Variable "X", num 6.)]]
        |> ignore

    [<Test>]
    let ``Given `factorial` solve with factorial(5, 120) should return true``() =
        insertFactorialRule (TestTerminal())
        |?> "factorial(5, 120)."
        |> expectedResult [[]]
        |> ignore

    [<Test>]
    let ``Given `factorial` solve with factorial(5, 121) should return false``() =
        insertFactorialRule (TestTerminal())
        |?> "factorial(5, 121)."
        |> expectedResult []
        |> ignore

[<TestFixture>]
module ParsedFactTests =
    [<Test>]
    let ``Given `test(1). test(2).` solve with test(X) should return [X = 1], [X = 2]``() =
        TestTerminal()
        |-> "test(1)."
        |-> "test(2)."
        |?> "test(X)."
        |> expectedResult [[(Variable "X", num 1.)]; [(Variable "X", num 2.)]]
        |> ignore
        
[<TestFixture>]
module ParsedListTests =
    let insertHeadRule terminal =
        terminal
        //|-> "head(H, L) :- [H | R] = L."
        |-> "head(X, [X | T])."
        
    let insertTailRule terminal =
        terminal
        //|-> "tail(T, L) :- [T1 | T] = L." // Could be used with wildcard variable
        |-> "tail(T, [X | T])."
        
    let insertMemberRule terminal =
        terminal
//        |-> "member(E, L) :- head(E, L)."
//        |-> "member(E, L) :- tail(T, L), member(E, T)."
        
    [<Test>]
    let ``Given `head` solve with head(X, []) should return false``() =
        TestTerminal()
        |> insertHeadRule
        |?> "head(X, [])."
        |> expectedResult []
        |> ignore
        
    [<Test>]
    let ``Given `head` solve with head(X, [1, 2, 3]) should return [X = 1]``() =
        TestTerminal()
        |> insertHeadRule
        |?> "head(X, [1, 2, 3])."
        |> expectedResult [[(Variable "X", num 1.)]]
        |> ignore
        
    [<Test>]
    let ``Given `tail` solve with tail(X, []) should return false``() =
        TestTerminal()
        |> insertTailRule
        |?> "tail(X, [])."
        |> expectedResult []
        |> ignore
        
    [<Test>]
    let ``Given `tail` solve with tail(X, [1]) should return [X = []]``() =
        TestTerminal()
        |> insertTailRule
        |?> "tail(X, [1])."
        |> expectedResult [[(Variable "X", numList [])]]
        |> ignore
        
    [<Test>]
    let ``Given `tail` solve with tail(X, [1, 2, 3]) should return [X = [2, 3]]``() =
        TestTerminal()
        |> insertTailRule
        |?> "tail(X, [1, 2, 3])."
        |> expectedResult [[(Variable "X", numList [2.; 3.])]]
        |> ignore
        
    [<Test>]
    let ``Given `member` solve with member(X, []) should return false``() =
        TestTerminal()
        |> insertHeadRule
        |> insertTailRule
        |> insertMemberRule
        |?> "member(X, [])."
        |> expectedResult []
        |> ignore
        
    [<Test>]
    let ``Given `member` solve with member(X, [1, 2]) should return [X = 1], [X = 2]``() =
        TestTerminal()
        |> insertHeadRule
        |> insertTailRule
        |> insertMemberRule
        |?> "member(X, [1, 2])."
        |> expectedResult [[(Variable "X", num 1.)]; [(Variable "X", num 2.)]]
        |> ignore
        
    [<Test>]
    let ``Given `member` solve with member(1, [1, 2]) should return true``() =
        TestTerminal()
        |> insertHeadRule
        |> insertTailRule
        |> insertMemberRule
        |?> "member(1, [1, 2])."
        |> expectedResult [[]]
        |> ignore
        
    [<Test>]
    let ``Given `member` solve with member(2, [1, 2]) should return true``() =
        TestTerminal()
        |> insertHeadRule
        |> insertTailRule
        |> insertMemberRule
        |?> "member(2, [1, 2])."
        |> expectedResult [[]]
        |> ignore
        
    [<Test>]
    let ``Given `member` solve with `L = [1, 2], member(2, L).` should return [L = [1, 2]] ``() =
        TestTerminal()
        |> insertHeadRule
        |> insertTailRule
        |> insertMemberRule
        |?> "L = [1, 2], member(2, L)."
        |> expectedResult [[(Variable "L", numList [1.; 2.])]]
        |> ignore

    [<Test>]
    let ``Given `member. list([1, 2]).` solve with `list(L), member(2, L).` should return [L = [1, 2]]``() =
        TestTerminal()
        |> insertHeadRule
        |> insertTailRule
        |> insertMemberRule
        |-> "list([1, 2])."
        |?> "L = [1, 2], member(2, L)."
        |> expectedResult [[(Variable "L", numList [1.; 2.])]]
        |> ignore

    [<Test>]
    let ``Given `member. list([1, 2]).` solve with `member(2, L), list(L).` should return [L = [1, 2]]``() =
        TestTerminal()
        |> insertHeadRule
        |> insertTailRule
        |> insertMemberRule
        |-> "list([1, 2])."
        |?> "L = [1, 2], member(2, L)."
        |> expectedResult [[(Variable "L", numList [1.; 2.])]]
        |> ignore
