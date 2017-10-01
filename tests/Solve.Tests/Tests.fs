module Solve.Tests

open NUnit.Framework
open System.Diagnostics

open Solve

open Types
open Types.Transformers

open Rule
open Rule.Transformers

[<DebuggerStepThrough>]
let inline fail() = failwith ""
[<DebuggerStepThrough>]
let inline check (expected: 'a) (actual: 'a) = Assert.AreEqual(expected, actual)

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
module VariableUnifyTests =
    let getChangeVariableFunction var n =
        function
        | Variable(v) when v = var -> sn n
        | v -> AnyVariable(v)
        
    [<Test>]
    let ``process struct test``() =
        let changeVariable = getChangeVariableFunction "N" 1.
        VariableUnify.processStruct changeVariable (Struct("test", [sv "N1"; sv "N"; sv "N"]))
        |> check (Struct("test", [sv "N1"; sn 1.; sn 1.]))
        
    [<Test>]
    let ``unify two any test``() =
        let checkFromVariableUnify a b =
            VariableUnify.unifyTwoAny a b |> check (Some b)
            VariableUnify.unifyTwoAny b a |> check (Some b)
        checkFromVariableUnify (sv "N") (sv "N")
        checkFromVariableUnify (sv "N") (sn 1.)
        checkFromVariableUnify (sv "N") (AnyStruct(Struct("123", [sv "N1"])))

        VariableUnify.unifyTwoAny (sv "N") (sv "N") |> check (Some(sv "N"))
        checkFromVariableUnify (sn 1.) (sn 1.)
        VariableUnify.unifyTwoAny (sn 1.) (sn 2.) |> check None

    [<Test>]
    let ``post unify unary expressions``() =
        let changeVariable = getChangeVariableFunction "N" 10.
        
        VariableUnify.postUnifyUnaryExpressions (sn 10.) (sn 5.) changeVariable (Variable("N"))
        |> check (sn 10.)
        VariableUnify.postUnifyUnaryExpressions (sn 10.) (sn 5.) changeVariable (Variable("N2"))
        |> check (sv "N2")
        VariableUnify.postUnifyUnaryExpressions (sv "N") (sn 5.) changeVariable (Variable("N"))
        |> check (sn 5.)
        VariableUnify.postUnifyUnaryExpressions (sv "N") (sv "N2") changeVariable (Variable("N"))
        |> check (sv "N2")

    [<Test>]
    let ``post unify binary expression test``() =
        let changeVariable = getChangeVariableFunction "N" 10.
        let proc e =
            match e with
            | (AnyTyped(TypedSNumber(SNumber(e1))), AnyTyped(TypedSNumber(SNumber(e2)))) -> e1 + e2
            | _ -> fail()
            
        VariableUnify.postUnifyBinaryExpression changeVariable proc (sn 10.) (sn 10.)
        |> check 20.
        VariableUnify.postUnifyBinaryExpression changeVariable proc (sv "N") (sn 10.)
        |> check 20.
        VariableUnify.postUnifyBinaryExpression changeVariable proc (sn 10.) (sv "N")
        |> check 20.
        
    [<Test>]
    let ``post unify binary expressions test``() =
        let changeVariable = getChangeVariableFunction "N" 10.
        
        VariableUnify.postUnifyBinaryExpressions (sn 10., sn 10.) (sn 5., sn 5.) changeVariable (Variable("N"))
        |> check (sn 10.)
        VariableUnify.postUnifyBinaryExpressions (sn 10., sn 10.) (sn 5., sn 5.) changeVariable (Variable("N2"))
        |> check (sv "N2")
        VariableUnify.postUnifyBinaryExpressions (sv "N", sn 10.) (sn 5., sn 5.) changeVariable (Variable("N"))
        |> check (sn 5.)
        VariableUnify.postUnifyBinaryExpressions (sn 10., sv "N") (sn 5., sn 5.) changeVariable (Variable("N"))
        |> check (sn 5.)
        VariableUnify.postUnifyBinaryExpressions (sv "N", sn 10.) (sv "N2", sn 5.) changeVariable (Variable("N"))
        |> check (sv "N2")
        VariableUnify.postUnifyBinaryExpressions (sn 10., sv "N") (sn 5., sv "N2") changeVariable (Variable("N"))
        |> check (sv "N2")
        
    [<Test>]
    let ``post unify params with arguments test3``() =
        VariableUnify.unifyParamsWithArguments [snp 10.; snp 5.; vp "V"] [sna 10.; sna 5.; va "V"]
        |> check (Some([sn 10.; sn 5.; sv "V"]))
        VariableUnify.unifyParamsWithArguments [snp 10.; snp 5.; vp "V"] [va "V"; va "V"; va "V"]
        |> check (Some([sn 10.; sn 5.; sv "V"]))
        VariableUnify.unifyParamsWithArguments [vp "V"; vp "V"; vp "V"] [sna 10.; sna 5.; va "V"]
        |> check (Some([sn 10.; sn 5.; sv "V"]))

        VariableUnify.unifyParamsWithArguments [vp "N"] [va "N2"] |> check (Some([sv "N"]))
        VariableUnify.unifyParamsWithArguments [snp 1.] [va "N"] |> check (Some([sn 1.]))
        VariableUnify.unifyParamsWithArguments [vp "N"] [sna 1.] |> check (Some([sn 1.]))
        VariableUnify.unifyParamsWithArguments [snp 1.] [sna 1.] |> check (Some([sn 1.]))
        VariableUnify.unifyParamsWithArguments [snp 1.] [sna 2.] |> check None

[<TestFixture>]
module SimpleTests =
    open VariableUnify
    open ExpressionUnify

    [<Test>]
    let testUnifyExpression() = 
        unifyExpression (EqExpr(sv "N", sn 1.)) (fun (Variable(v)) -> sn 1.)
        |> check (EqExpr(sn 1., sn 1.))
        unifyExpression (EqExpr(sv "N", sv "N2")) (fun (Variable(v)) -> if v = "N" then sn 1. else sn 2.)
        |> check (EqExpr(sn 1., sn 2.))
        unifyExpression (EqExpr(sv "N", sv "N2")) (fun (Variable(v)) -> if v = "N" then sn 1. else sv v)
        |> check (EqExpr(sn 1., sv "N2"))
    
    [<Test>]
    let testUnifyRule() = 
        unifyRule (Rule(Signature("eq1", [vp "N"]), (EqExpr(sv "N", sn 1.)))) [sna 1.]
        |> check (Some(Rule(Signature("eq1", [snp 1.]), (EqExpr(sn 1., sn 1.)))))
    
    open Execute

    [<Test>]
    let testExecuteCalc() = 
        executeCalc (Value(CalcAny(sn 1.)))
        |> check (SNumber(1.))

        executeCalc (Plus(CalcAny(sn 1.), CalcAny(sn 1.)))
        |> check (SNumber(2.))
    
    [<Test>]
    let testExecuteExpression() = 
        let executeCustom a = failwith "unexpected input"
    
        executeExpression (EqExpr(sv "N", sn 1.)) executeCustom (fun v -> sn 1.)
        |> check [EqExpr(sn 1., sn 1.)]
        executeExpression (EqExpr(sv "N", sn 1.)) executeCustom (fun v -> AnyVariable(v))
        |> check [EqExpr(sn 1., sn 1.)]
        executeExpression (AndExpression(CalcExpr(sv "N", Value(CalcAny(sn 1.))), EqExpr(sv "N", sn 1.))) executeCustom (fun v -> sn 1.)
        |> check [AndExpression(CalcExpr(sn 1., Value(CalcAny(sn 1.))), EqExpr(sn 1., sn 1.))]

    open Solve

    [<Test>]
    let testExecute() = 
        solve (goal("eq1", [va "N"])) [Rule(Signature("eq1", [vp "N"]), (EqExpr(sv "N", sn 1.)))]
        |> check [[sn 1.]]

        solve (goal("eq2", [sna 1.])) [Rule(Signature("eq2", [vp "N"]), (EqExpr(sv "N", sn 1.)))]
        |> check [[sn 1.]]

        solve (goal("eq3", [sna 2.])) [Rule(Signature("eq3", [vp "N"]), (EqExpr(sv "N", sn 1.)))]
        |> check []
            
        solve (goal("and", [va "N"])) [Rule(Signature("and", [vp "N"]), (AndExpression(EqExpr(sv "N", sn 1.), EqExpr(sv "N", sn 2.))))]
        |> check []

        solve (goal("or", [va "N"])) [Rule(Signature("or", [vp "N"]), (OrExpression(EqExpr(sv "N", sn 1.), EqExpr(sv "N", sn 2.))))]
        |> check [[sn 1.]; [sn 2.]]

        solve (goal("fa", [va "N"])) [Rule(Signature("fa", [vp "N"]), (False))]
        |> check []

        solve (goal("innervar", [va "N"])) [Rule(Signature("innervar", [vp "N"]), (AndExpression(EqExpr(sv "Temp", sn 1.), EqExpr(sv "N", sv "Temp"))))]
        |> check [[sn 1.]]

    [<Test>]
    let realTest() =
        solve (goal("eq1_both", [va "N"; va "Res"])) [Rule(Signature("eq1_both", [vp "N1"; vp "N2"]), (AndExpression((EqExpr(sv "N1", sn 1.), (EqExpr(sv "N2", sn 1.))))))]
        |> check [[sn 1.; sn 1.]]
        solve(goal("eq", [va "N"; va "N2"])) [Rule(Signature("eq", [vp "N1"; vp "N2"]), (EqExpr(sv "N1", sv "N2")))]
        |> check [[sv "N2"; sv "N2"]]

        let pseudoFactorialRule = Rule(Signature("f1", [vp "N"; vp "Res"]), OrExpression(AndExpression(EqExpr(sv "N", sn 1.), EqExpr(sv "Res", sn 1.)), AndExpression(GrExpr(sv "N", sn 1.), EqExpr(sv "Res", sn 2.))))
        solve (goal("f1", [sna 1.; va "Res"])) [pseudoFactorialRule]
        |> check [[sn 1.; sn 1.]]
        solve (goal("f1", [sna 3.; va "Res"])) [pseudoFactorialRule]
        |> check [[sn 3.; sn 2.]]

        let getN = Rule(Signature("getn", [vp "R"]), EqExpr(sv "R", sn 1.))
        let inn = Rule(Signature("inn", [vp "Res"]), CallExpression(Goal(Struct("getn", [sv "Res"]))))
        solve (goal("inn", [va "R"])) [getN; inn]
        |> check [[sn 1.]]

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
        |> check [[stringAny "Polina"]]
        solve (goal("person", [va "X"])) knowledgebase
        |> check [[stringAny "Mary"]; [stringAny "Polina"]; [stringAny "Evgeniy"]; [stringAny "Solniwko"]]
        solve (goal("person", [Argument(stringAny "Miwa")])) knowledgebase
        |> check []

    [<Test>]
    let testParentRule() =
        solve (goal("parent", [Argument(stringAny "Polina"); va "Descendant"])) knowledgebase
        |> check [[stringAny "Polina"; stringAny "Evgeniy"]]
        solve (goal("parent", [va "Parent"; va "Descendant"])) knowledgebase
        |> check [[stringAny "Mary"; stringAny "Polina"]; [stringAny "Solniwko"; stringAny "Polina"]; [stringAny "Polina"; stringAny "Evgeniy"]]

    [<Test>]
    let testGrandparentRule() =
        solve (goal("grandparent", [va "GrandParent"; va "Descendant"])) knowledgebase
        |> check [[stringAny "Mary"; stringAny "Evgeniy"]; [stringAny "Solniwko"; stringAny "Evgeniy"]]
        solve (goal("grandparent", [Argument(stringAny "Mary"); Argument(stringAny "Evgeniy")])) knowledgebase
        |> check [[stringAny "Mary"; stringAny "Evgeniy"]]