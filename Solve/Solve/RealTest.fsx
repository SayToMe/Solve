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

module RealTestModule =
    let getPersonFact p = Rule(Signature("person", [charP p]), True)

    ExecutionModule.execute (Goal("person", [charA 'M'])) (getPersonFact 'M')

    ExecutionModule.checkGoal (Goal("person", [charA 'M'])) [getPersonFact 'M'; getPersonFact 'M']
    ExecutionModule.checkGoal (Goal("person", [va "X"])) [getPersonFact 'M'; getPersonFact 'C']