module Solve.Tests

open NUnit.Framework
open System.Diagnostics

open Solve

open Types
open Types.Transformers

open Rule
open Rule.Transformers

[<DebuggerStepThrough>]
let inline check errorName (expected: 'a) (actual: 'a) = Assert.AreEqual(expected, actual, errorName)// if actual = expected then expected else (failwithf "%s. %O != %O" errorName actual expected)

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

[<DebuggerStepThrough>]
let goal (name, args) = Goal(Struct(name, fromArgs args))

[<TestFixture>]
module SimpleTests =
    open VariableUnify
    open ExpressionUnify

    [<Test>]
    let testUnifyParamsWithArguments() =
        unifyParamsWithArguments [vp "N"] [va "N2"] |> check "u1" (Some([sv "N"]))
        unifyParamsWithArguments [snp 1.] [va "N"] |> check "u2" (Some([sn 1.]))
        unifyParamsWithArguments [vp "N"] [sna 1.] |> check "u3" (Some([sn 1.]))
        unifyParamsWithArguments [snp 1.] [sna 1.] |> check "u4" (Some([sn 1.]))
        unifyParamsWithArguments [snp 1.] [sna 2.] |> check "u5" None

    [<Test>]
    let testUnifyExpression() = 
        unifyExpression (EqExpr(sv "N", sn 1.)) (fun (Variable(v)) -> sn 1.)
        |> check "unif1" (EqExpr(sn 1., sn 1.))
        unifyExpression (EqExpr(sv "N", sv "N2")) (fun (Variable(v)) -> if v = "N" then sn 1. else sn 2.)
        |> check "unif2" (EqExpr(sn 1., sn 2.))
        unifyExpression (EqExpr(sv "N", sv "N2")) (fun (Variable(v)) -> if v = "N" then sn 1. else sv v)
        |> check "unif3" (EqExpr(sn 1., sv "N2"))
    
    [<Test>]
    let testUnifyRule() = 
        unifyRule (Rule(Signature("eq1", [vp "N"]), (EqExpr(sv "N", sn 1.)))) [sna 1.]
        |> check "rule1" (Some(Rule(Signature("eq1", [snp 1.]), (EqExpr(sn 1., sn 1.)))))
    
    open Execute

    [<Test>]
    let testExecuteCalc() = 
        executeCalc (Value(CalcAny(sn 1.)))
        |> check "calc1" (SNumber(1.))

        executeCalc (Plus(CalcAny(sn 1.), CalcAny(sn 1.)))
        |> check "calc2" (SNumber(2.))
    
    [<Test>]
    let testExecuteExpression() = 
        let executeCustom a = failwith "unexpected input"
    
        executeExpression (EqExpr(sv "N", sn 1.)) executeCustom (fun v -> sn 1.)
        |> check "ex exp1" [EqExpr(sn 1., sn 1.)]
        executeExpression (EqExpr(sv "N", sn 1.)) executeCustom (fun v -> AnyVariable(v))
        |> check "ex exp1" [EqExpr(sn 1., sn 1.)]
        executeExpression (AndExpression(CalcExpr(sv "N", Value(CalcAny(sn 1.))), EqExpr(sv "N", sn 1.))) executeCustom (fun v -> sn 1.)
        |> check "ex exp3" [AndExpression(CalcExpr(sn 1., Value(CalcAny(sn 1.))), EqExpr(sn 1., sn 1.))]

    open Solve

    [<Test>]
    let testExecute() = 
        solve (goal("eq1", [va "N"])) [Rule(Signature("eq1", [vp "N"]), (EqExpr(sv "N", sn 1.)))]
        |> check "execute1" [[sn 1.]]

        solve (goal("eq2", [sna 1.])) [Rule(Signature("eq2", [vp "N"]), (EqExpr(sv "N", sn 1.)))]
        |> check "execute2" [[sn 1.]]

        solve (goal("eq3", [sna 2.])) [Rule(Signature("eq3", [vp "N"]), (EqExpr(sv "N", sn 1.)))]
        |> check "execute3" []
            
        solve (goal("and", [va "N"])) [Rule(Signature("and", [vp "N"]), (AndExpression(EqExpr(sv "N", sn 1.), EqExpr(sv "N", sn 2.))))]
        |> check "execute3" []

        solve (goal("or", [va "N"])) [Rule(Signature("or", [vp "N"]), (OrExpression(EqExpr(sv "N", sn 1.), EqExpr(sv "N", sn 2.))))]
        |> check "execute3" [[sn 1.]; [sn 2.]]

        solve (goal("fa", [va "N"])) [Rule(Signature("fa", [vp "N"]), (False))]
        |> check "false check" []

        solve (goal("innervar", [va "N"])) [Rule(Signature("innervar", [vp "N"]), (AndExpression(EqExpr(sv "Temp", sn 1.), EqExpr(sv "N", sv "Temp"))))]
        |> check "innervar not supported" [[sn 1.]]

    [<Test>]
    let realTest() =
        solve (goal("eq1_both", [va "N"; va "Res"])) [Rule(Signature("eq1_both", [vp "N1"; vp "N2"]), (AndExpression((EqExpr(sv "N1", sn 1.), (EqExpr(sv "N2", sn 1.))))))]
        |> check "and test1" [[sn 1.; sn 1.]]
        solve(goal("eq", [va "N"; va "N2"])) [Rule(Signature("eq", [vp "N1"; vp "N2"]), (EqExpr(sv "N1", sv "N2")))]
        |> check "eq test" [[sv "N2"; sv "N2"]]

        let pseudoFactorialRule = Rule(Signature("f1", [vp "N"; vp "Res"]), OrExpression(AndExpression(EqExpr(sv "N", sn 1.), EqExpr(sv "Res", sn 1.)), AndExpression(GrExpr(sv "N", sn 1.), EqExpr(sv "Res", sn 2.))))
        solve (goal("f1", [sna 1.; va "Res"])) [pseudoFactorialRule]
        |> check "f1" [[sn 1.; sn 1.]]
        solve (goal("f1", [sna 3.; va "Res"])) [pseudoFactorialRule]
        |> check "f2" [[sn 3.; sn 2.]]

[<TestFixture>]
module RuleTests =
    let person p = Rule(Signature("person", [Parameter(stringAny p)]), True)
    let parent p d = Rule(Signature("parent", [Parameter(stringAny p); Parameter(stringAny d)]), True)
    let grandparent = Rule(Signature("grandparent", [vp "G"; vp "D"]), AndExpression(CallExpression(goal("parent", [va "G"; va "P"])), CallExpression(goal("parent", [va "P"; va "D"]))))

    let knowledgebase = [
        person "Mary";
        person "Polina";
        person "Evgeniy";
        person "Solniwko";
    
        parent "Mary" "Polina";
        parent "Solniwko" "Polina";
        parent "Polina" "Evgeniy";

        grandparent
    ]

    [<Test>]
    let testPersonRule() =
        solve (goal("person", [Argument(stringAny "Polina")])) knowledgebase
        |> check "check polina" [[stringAny "Polina"]]
        solve (goal("person", [va "X"])) knowledgebase
        |> check "check people" [[stringAny "Mary"]; [stringAny "Polina"]; [stringAny "Evgeniy"]; [stringAny "Solniwko"]]
        solve (goal("person", [Argument(stringAny "Miwa")])) knowledgebase
        |> check "check missing person" []

    [<Test>]
    let testParentRule() =
        solve (goal("parent", [Argument(stringAny "Polina"); va "Descendant"])) knowledgebase
        |> check "check defined parent" [[stringAny "Polina"; stringAny "Evgeniy"]]
        solve (goal("parent", [va "Parent"; va "Descendant"])) knowledgebase
        |> check "check all parents" [[stringAny "Mary"; stringAny "Polina"]; [stringAny "Solniwko"; stringAny "Polina"]; [stringAny "Polina"; stringAny "Evgeniy"]]

    [<Test>]
    let testGrandparentRule() =
        solve (goal("grandparent", [va "GrandParent"; va "Descendant"])) knowledgebase
        |> check "check all parents" [[stringAny "Mary"; stringAny "Evgeniy"]; [stringAny "Solniwko"; stringAny "Evgeniy"]]
        solve (goal("grandparent", [Argument(stringAny "Mary"); Argument(stringAny "Evgeniy")])) knowledgebase
        |> check "check defined parent" [[stringAny "Mary"; stringAny "Evgeniy"]]