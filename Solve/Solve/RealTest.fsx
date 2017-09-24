#load "Main.fs"

open Solve
open System.Diagnostics

[<DebuggerStepThrough>]
let check errorName expected actual = if actual = expected then expected else (failwithf "%s. %O != %O" errorName actual expected)

[<DebuggerStepThrough>]
let sn x = AnyTyped(TypedSNumber(SNumber x))
[<DebuggerStepThrough>]
let sv x = AnyVariable(Variable(x))

[<DebuggerStepThrough>]
let snp x = Parameter(sn x)
[<DebuggerStepThrough>]
let vp n = Parameter(AnyVariable(Variable(n)))
[<DebuggerStepThrough>]
let charP c = Parameter(AnyTyped(TypedSChar(SChar(c))))

[<DebuggerStepThrough>]
let sna x = Argument(sn x)
[<DebuggerStepThrough>]
let va n = Argument(AnyVariable(Variable(n)))
[<DebuggerStepThrough>]
let charA c = Argument(AnyTyped(TypedSChar(SChar(c))))

[<DebuggerStepThrough>]
let charAny c = AnyTyped(TypedSChar(SChar(c)))

[<DebuggerStepThrough>]
let stringAny (str: string) = AnyTyped(TypedSList(SList(str.ToCharArray() |> Array.map (SChar >> TypedSChar) |> Array.toList)))

let formatResult (result: Any list list) =
    let format fn =
        function
        | [] -> "[]"
        | [h] -> "[" + fn h + "]"
        | list -> "[" + (List.fold (fun acc n -> if acc = "" then fn n else acc + ", " + fn n) "" list) + "]"

    format (format formatAny) result

// RealTests
let person p = Rule(Signature("person", [Parameter(stringAny p)]), True)
let parent p d = Rule(Signature("parent", [Parameter(stringAny p); Parameter(stringAny d)]), True)
let grandparent = Rule(Signature("grandparent", [vp "G"; vp "D"]), AndExpression(CallExpression(Goal("parent", [va "G"; va "P"])), CallExpression(Goal("parent", [va "P"; va "D"]))))

let knowledgebase = [
    person "Mary";
    person "Polina";
    person "Evgeniy";
    person "Solniwko";

    parent "Mary" "Polina";
    parent "Polina" "Evgeniy";

    grandparent
]

ExecutionModule.checkGoal (Goal("person", [Argument(stringAny "Polina")])) knowledgebase |> formatResult
ExecutionModule.checkGoal (Goal("person", [va "X"])) knowledgebase |> formatResult
ExecutionModule.checkGoal (Goal("person", [Argument(stringAny "Miwa")])) knowledgebase |> formatResult

ExecutionModule.checkGoal (Goal("parent", [Argument(stringAny "Polina"); va "Descendant"])) knowledgebase |> formatResult
ExecutionModule.checkGoal (Goal("parent", [va "Parent"; va "Descendant"])) knowledgebase |> formatResult

ExecutionModule.checkGoal (Goal("grandparent", [va "GrandParent"; va "Descendant"])) knowledgebase |> formatResult

ExecutionModule.checkGoal (Goal("grandparent", [Argument(stringAny "Mary"); Argument(stringAny "Evgeniy")])) knowledgebase |> formatResult