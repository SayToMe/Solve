#load "Main.fs"

open Solve

let check errorName expected actual = if actual = expected then expected else (failwithf "%s. %O != %O" errorName actual expected)

let sn x = AnyTyped(TypedSNumber(SNumber x))
let sv x = AnyVariable(Variable(x))

let snp x = Parameter(sn x)
let vp n = Parameter(AnyVariable(Variable(n)))
let charP c = Parameter(AnyTyped(TypedSChar(SChar(c))))

let sna x = Argument(sn x)
let va n = Argument(AnyVariable(Variable(n)))
let charA c = Argument(AnyTyped(TypedSChar(SChar(c))))

let charAny c = AnyTyped(TypedSChar(SChar(c)))

let stringAny (str: string) = AnyTyped(TypedSList(SList(str.ToCharArray() |> Array.map (SChar >> TypedSChar) |> Array.toList)))

module RealTestModule =
    let person p = Rule(Signature("person", [Parameter(stringAny p)]), True)
    let parent p d = Rule(Signature("parent", [Parameter(stringAny p); Parameter(stringAny d)]), True)
    let grandparent = Rule(Signature("grandparent", [vp "G"; vp "D"]), AndExpression(CallExpression(Goal("parent", [va "G"; va "P"])), CallExpression(Goal("parent", [va "P"; va "D"]))))

    let knowledgebase = [
        person "Mary";
        person "Polina";
        person "Evgeniy";
        person "Solniwko";

        parent "Mary" "Polina";
        parent "Polina" "Engeniy";

        grandparent
    ]
    
    ExecutionModule.checkGoal (Goal("person", [Argument(stringAny "Polina")])) knowledgebase
    ExecutionModule.checkGoal (Goal("person", [va "X"])) knowledgebase
    ExecutionModule.checkGoal (Goal("person", [Argument(stringAny "Miwa")])) knowledgebase

    ExecutionModule.checkGoal (Goal("parent", [Argument(stringAny "Polina"); va "Descendant"])) knowledgebase
    ExecutionModule.checkGoal (Goal("parent", [va "Parent"; va "Descendant"])) knowledgebase

    ExecutionModule.checkGoal (Goal("grandparent", [va "GrandParent"; va "Descendant"])) knowledgebase