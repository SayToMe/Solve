module Solve.Tests

open NUnit.Framework
open System.Diagnostics

open Solve

open TermTypes
open TermTypes.Transformers

open Rule
open Rule.Transformers

[<DebuggerStepThrough>]
let inline fail() = failwith ""
[<DebuggerStepThrough>]
let inline check (expected: 'a) (actual: 'a) = 
    Assert.AreEqual(expected, actual, sprintf "%O != %O" expected actual)
[<DebuggerStepThrough>]
let inline checkExecuteExpression expected actual =
    check expected (Seq.toList actual)
[<DebuggerStepThrough>]
let inline checkSolve expected actual =
    check expected (actual |> Seq.map (Seq.toList) |> Seq.toList)

[<DebuggerStepThrough>]
let sn x = TypedTerm(TypedNumberTerm(NumberTerm x))
[<DebuggerStepThrough>]
let sv x = VariableTerm(Variable(x))

[<DebuggerStepThrough>]
let snp x = Parameter(sn x)
[<DebuggerStepThrough>]
let vp n = Parameter(VariableTerm(Variable(n)))
[<DebuggerStepThrough>]
let charP c = Parameter(TypedTerm(TypedCharTerm(CharTerm(c))))

[<DebuggerStepThrough>]
let sna x = Argument(sn x)
[<DebuggerStepThrough>]
let va n = Argument(VariableTerm(Variable(n)))
[<DebuggerStepThrough>]
let charA c = Argument(TypedTerm(TypedCharTerm(CharTerm(c))))

[<DebuggerStepThrough>]
let charAny c = TypedTerm(TypedCharTerm(CharTerm(c)))

[<DebuggerStepThrough>]
let stringAny (str: string) = TypedTerm(TypedListTerm(ListTerm(str.ToCharArray() |> Array.map (CharTerm >> TypedCharTerm) |> Array.toList)))

[<DebuggerStepThrough>]
let goal (name, args) = Goal(Structure(name, fromArgs args))

[<AutoOpen>]
module NUnitExtensions =
    open System

    type ReportAttribute() =
        inherit TestActionAttribute()
        
        let mutable _timer = Stopwatch()
        let mutable _gcmem = 0L
        let mutable _gc = []
        
        override __.Targets = ActionTargets.Test

        override __.BeforeTest test = 
            System.AppDomain.MonitoringIsEnabled <- true

            _timer.Start()
            GC.Collect()
            _gcmem <- AppDomain.CurrentDomain.MonitoringTotalAllocatedMemorySize
            // gc executes one or zero times after starting no gc region on a different systems
            _gc <- [0..2] |> List.map (fun i -> GC.CollectionCount(i) + 1)

        override __.AfterTest test = 
            _timer.Stop()
            let gcm = AppDomain.CurrentDomain.MonitoringTotalAllocatedMemorySize
            
            let gc = [0..2] |> List.map (fun i -> GC.CollectionCount(i))
            let [gc0; gc1; gc2] = List.map2 (fun prev cur -> max (cur - prev) 0) _gc gc

            let gcResult = sprintf "GC collects: %d %d %d Allocated: %d KB" gc0 gc1 gc2 ((gcm - _gcmem) / 1024L)
            let timeResult = sprintf "Took %f ms" _timer.Elapsed.TotalMilliseconds

            Console.WriteLine(sprintf "***** Test %s. %s. %s." test.FullName timeResult gcResult)

[<TestFixture>]
module ReferenceTests =
    [<Test; Report>]
    let ``reference test``() =
        [1..100] |> List.iter (fun _ -> [1..10000] |> List.fold (+) 0 |> fun x -> Assert.Greater(x, 0))

[<TestFixture>]
module VariableUnifyTests =
    let getChangeVariableFunction var n =
        function
        | Variable(v) when v = var -> sn n
        | v -> VariableTerm(v)

    [<Test; Report>]
    let ``process struct test``() =
        let changeVariable = getChangeVariableFunction "N" 1.
        VariableUnify.processStruct changeVariable (Structure("test", [sv "N1"; sv "N"; sv "N"]))
        |> check (Structure("test", [sv "N1"; sn 1.; sn 1.]))
        
    [<Test; Report>]
    let ``unify two any test``() =
        let checkFromVariableUnify a b =
            VariableUnify.unifyTwoAny a b |> check (Some b)
            VariableUnify.unifyTwoAny b a |> check (Some b)
        checkFromVariableUnify (sv "N") (sv "N")
        checkFromVariableUnify (sv "N") (sn 1.)
        checkFromVariableUnify (sv "N") (StructureTerm(Structure("123", [sv "N1"])))

        VariableUnify.unifyTwoAny (sv "N") (sv "N") |> check (Some(sv "N"))
        checkFromVariableUnify (sn 1.) (sn 1.)
        VariableUnify.unifyTwoAny (sn 1.) (sn 2.) |> check None

    [<Test; Report>]
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

    [<Test; Report>]
    let ``post unify binary expression test``() =
        let changeVariable = getChangeVariableFunction "N" 10.
        let proc e =
            match e with
            | (TypedTerm(TypedNumberTerm(NumberTerm(e1))), TypedTerm(TypedNumberTerm(NumberTerm(e2)))) -> e1 + e2
            | _ -> fail()
            
        VariableUnify.postUnifyBinaryExpression changeVariable proc (sn 10.) (sn 10.)
        |> check 20.
        VariableUnify.postUnifyBinaryExpression changeVariable proc (sv "N") (sn 10.)
        |> check 20.
        VariableUnify.postUnifyBinaryExpression changeVariable proc (sn 10.) (sv "N")
        |> check 20.
        
    [<Test; Report>]
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
        
    [<Test; Report>]
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

    [<Test; Report>]
    let testUnifyExpression() = 
        unifyExpression (EqExpr(sv "N", sn 1.)) (fun (Variable(v)) -> sn 1.)
        |> check (EqExpr(sn 1., sn 1.))
        unifyExpression (EqExpr(sv "N", sv "N2")) (fun (Variable(v)) -> if v = "N" then sn 1. else sn 2.)
        |> check (EqExpr(sn 1., sn 2.))
        unifyExpression (EqExpr(sv "N", sv "N2")) (fun (Variable(v)) -> if v = "N" then sn 1. else sv v)
        |> check (EqExpr(sn 1., sv "N2"))
    
    [<Test; Report>]
    let testUnifyRule() = 
        unifyRule (Rule(Signature("eq1", [vp "N"]), (EqExpr(sv "N", sn 1.)))) [sna 1.]
        |> check (Some(Rule(Signature("eq1", [snp 1.]), (EqExpr(sn 1., sn 1.)))))
    
    open Execute

    [<Test; Report>]
    let testExecuteCalc() = 
        executeCalc (Value(CalcAny(sn 1.)))
        |> check (NumberTerm(1.))

        executeCalc (Plus(CalcAny(sn 1.), CalcAny(sn 1.)))
        |> check (NumberTerm(2.))
    
    [<Test; Report>]
    let testExecuteExpression() = 
        let executeCustom a = failwith "unexpected input"
    
        executeExpression (EqExpr(sv "N", sn 1.)) executeCustom (fun v -> sn 1.)
        |> checkExecuteExpression [EqExpr(sn 1., sn 1.)]
        executeExpression (EqExpr(sv "N", sn 1.)) executeCustom (fun v -> VariableTerm(v))
        |> checkExecuteExpression [EqExpr(sn 1., sn 1.)]
        executeExpression (AndExpression(CalcExpr(sv "N", Value(CalcAny(sn 1.))), EqExpr(sv "N", sn 1.))) executeCustom (fun v -> sn 1.)
        |> checkExecuteExpression [AndExpression(CalcExpr(sn 1., Value(CalcAny(sn 1.))), EqExpr(sn 1., sn 1.))]

    open Solve

    [<Test; Report>]
    let testExecute() = 
        solve (goal("eq1", [va "N"])) [Rule(Signature("eq1", [vp "N"]), (EqExpr(sv "N", sn 1.)))]
        |> checkSolve [[sn 1.]]

        solve (goal("eq2", [sna 1.])) [Rule(Signature("eq2", [vp "N"]), (EqExpr(sv "N", sn 1.)))]
        |> checkSolve [[sn 1.]]

        solve (goal("eq3", [sna 2.])) [Rule(Signature("eq3", [vp "N"]), (EqExpr(sv "N", sn 1.)))]
        |> checkSolve []
            
        solve (goal("and", [va "N"])) [Rule(Signature("and", [vp "N"]), (AndExpression(EqExpr(sv "N", sn 1.), EqExpr(sv "N", sn 2.))))]
        |> checkSolve []

        solve (goal("or", [va "N"])) [Rule(Signature("or", [vp "N"]), (OrExpression(EqExpr(sv "N", sn 1.), EqExpr(sv "N", sn 2.))))]
        |> checkSolve [[sn 1.]; [sn 2.]]

        solve (goal("fa", [va "N"])) [Rule(Signature("fa", [vp "N"]), (False))]
        |> checkSolve []

        solve (goal("innervar", [va "N"])) [Rule(Signature("innervar", [vp "N"]), (AndExpression(EqExpr(sv "Temp", sn 1.), EqExpr(sv "N", sv "Temp"))))]
        |> checkSolve [[sn 1.]]

        solve (goal("structure execute", [sna 2.; va "Res"])) [Rule(Signature("structure execute", [vp "N"; vp "R"]), CalcExpr(sv "R", Value(CalcAny(StructureTerm(Structure("+", [sv "N"; sn 1.]))))))]
        |> checkSolve [[sn 2.; sn 3.]]

    [<Test; Report>]
    let testCut() =
        solve (goal("cut", [va "R"])) [Rule(Signature("cut", [vp "R"]), (AndExpression(OrExpression(EqExpr(sv "R", sn 1.), EqExpr(sv "R", sn 2.)), Cut)))]
        |> checkSolve [[sn 1.]]

    [<Test; Report>]
    let testComplexCut() =
        solve (goal("cut", [va "R1"; va "R2"])) [Rule(Signature("cut", [vp "R1"; vp "R2"]), (AndExpression(AndExpression(OrExpression(EqExpr(sv "R1", sn 1.), EqExpr(sv "R1", sn 2.)), OrExpression(EqExpr(sv "R2", sn 1.), EqExpr(sv "R2", sn 2.))), Cut)))]
        |> checkSolve [[sn 1.; sn 1.]]

    [<Test; Report>]
    let checkLazySolve =
        solve (goal("lazy infinite", [sna 1.; va "R"])) [Rule(Signature("lazy infinite", [vp "C"; vp "R"]), OrExpression(EqExpr(sv "C", sv "R"), AndExpression(CalcExpr(sv "NextC", Plus(CalcAny(sv "C"), CalcAny(sn 1.))), CallExpression(Goal(Structure("lazy infinite", [sv "NextC"; sv "R"]))))))]
        |> Seq.take 10
        |> checkSolve ([1..10] |> List.map (fun x -> [sn 1.; sn (float x)]))

    [<Test; Report>]
    let realTest() =
        solve (goal("eq1_both", [va "N"; va "Res"])) [Rule(Signature("eq1_both", [vp "N1"; vp "N2"]), (AndExpression((EqExpr(sv "N1", sn 1.), (EqExpr(sv "N2", sn 1.))))))]
        |> checkSolve [[sn 1.; sn 1.]]
        solve(goal("eq", [va "N"; va "N2"])) [Rule(Signature("eq", [vp "N1"; vp "N2"]), (EqExpr(sv "N1", sv "N2")))]
        |> checkSolve [[sv "N2"; sv "N2"]]

        let oneOrTwoRule = Rule(Signature("f1", [vp "N"; vp "Res"]), OrExpression(AndExpression(EqExpr(sv "N", sn 1.), EqExpr(sv "Res", sn 1.)), AndExpression(GrExpr(sv "N", sn 1.), EqExpr(sv "Res", sn 2.))))
        solve (goal("f1", [sna 1.; va "Res"])) [oneOrTwoRule]
        |> checkSolve [[sn 1.; sn 1.]]
        solve (goal("f1", [sna 3.; va "Res"])) [oneOrTwoRule]
        |> checkSolve [[sn 3.; sn 2.]]

        let getN = Rule(Signature("getn", [vp "R"]), EqExpr(sv "R", sn 1.))
        let inn = Rule(Signature("inn", [vp "Res"]), CallExpression(Goal(Structure("getn", [sv "Res"]))))
        solve (goal("inn", [va "R"])) [getN; inn]
        |> checkSolve [[sn 1.]]
        
    [<Test; Report>]
    let factorialTest() =
        let leftOr = AndExpression(EqExpr(sv "N", sn 1.), EqExpr(sv "Res", sn 1.))
        let rightOr = AndExpression(GrExpr(sv "N", sn 1.), AndExpression(CalcExpr(sv "N1", Subsctruct(CalcAny(sv "N"), CalcAny(sn 1.))), AndExpression(CallExpression(Goal(Structure("factorial", [sv "N1"; sv "R1"]))), CalcExpr(sv "Res", Multiply(CalcAny(sv "R1"), CalcAny(sv "N"))))))
        let factorial = Rule(Signature("factorial", [vp "N"; vp "Res"]), OrExpression(leftOr, rightOr))

        let knowledgebase = [
            factorial
        ]
        
        let checkf n =
            let rec f x = if x = 1. then 1. else x * f(x - 1.)
            
            solve (goal("factorial", [sna n; va "Res"])) knowledgebase
            |> checkSolve [[sn n; sn (f n)]]

        [1..10] |> List.iter (float >> checkf)
        
    [<Test; Report>]
    let cutFactorialTest() =
        let leftOr = AndExpression(AndExpression(EqExpr(sv "N", sn 1.), EqExpr(sv "Res", sn 1.)), Cut)
        let rightOr = AndExpression(CalcExpr(sv "N1", Subsctruct(CalcAny(sv "N"), CalcAny(sn 1.))), AndExpression(CallExpression(Goal(Structure("factorial", [sv "N1"; sv "R1"]))), CalcExpr(sv "Res", Multiply(CalcAny(sv "R1"), CalcAny(sv "N")))))
        let factorial = Rule(Signature("factorial", [vp "N"; vp "Res"]), OrExpression(leftOr, rightOr))

        let knowledgebase = [
            factorial
        ]
        
        let checkf n =
            let rec f x = if x = 1. then 1. else x * f(x - 1.)
            
            solve (goal("factorial", [sna n; va "Res"])) knowledgebase
            |> checkSolve [[sn n; sn (f n)]]

        [1..10] |> List.iter (float >> checkf)

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

    [<Test; Report>]
    let testPersonRule() =
        solve (goal("person", [Argument(stringAny "Polina")])) knowledgebase
        |> checkSolve [[stringAny "Polina"]]
        solve (goal("person", [va "X"])) knowledgebase
        |> checkSolve [[stringAny "Mary"]; [stringAny "Polina"]; [stringAny "Evgeniy"]; [stringAny "Solniwko"]]
        solve (goal("person", [Argument(stringAny "Miwa")])) knowledgebase
        |> checkSolve []

    [<Test; Report>]
    let testParentRule() =
        solve (goal("parent", [Argument(stringAny "Polina"); va "Descendant"])) knowledgebase
        |> checkSolve [[stringAny "Polina"; stringAny "Evgeniy"]]
        solve (goal("parent", [va "Parent"; va "Descendant"])) knowledgebase
        |> checkSolve [[stringAny "Mary"; stringAny "Polina"]; [stringAny "Solniwko"; stringAny "Polina"]; [stringAny "Polina"; stringAny "Evgeniy"]]

    [<Test; ReportAttribute>]
    let testGrandparentRule() =
        solve (goal("grandparent", [va "GrandParent"; va "Descendant"])) knowledgebase
        |> checkSolve [[stringAny "Mary"; stringAny "Evgeniy"]; [stringAny "Solniwko"; stringAny "Evgeniy"]]
        solve (goal("grandparent", [Argument(stringAny "Mary"); Argument(stringAny "Evgeniy")])) knowledgebase
        |> checkSolve [[stringAny "Mary"; stringAny "Evgeniy"]]

    [<Test; ReportAttribute>]
    let bigTest() =
        let r = System.Random()
        let persons = [1..1000] |> List.map (fun i -> System.Guid.NewGuid().ToString()) |> List.map person
        let gerRuleName (Rule(Signature(name, _), _)) = name
        let rec generate genFn =
            let pi = r.Next(persons.Length)
            let ci = r.Next(persons.Length)
            if pi = ci then
                generate genFn
            else
                genFn (gerRuleName persons.[pi]) (gerRuleName persons.[ci])

        let parents = [1..1000] |> List.map (fun i -> generate parent)
        let kb = persons @ parents

        let toTest = [1..10000] |> List.map (fun i -> generate (fun p c -> (goal("parent", [va p; va c]))))

        toTest |> List.map (fun t -> solve t kb |> Seq.toList) |> ignore