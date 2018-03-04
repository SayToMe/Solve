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
let inline SIGNATURE name terms = Signature(name, toParams terms)
[<DebuggerStepThrough>]
let inline RULE signature body = Rule(signature, body)
[<DebuggerStepThrough>]
let inline GOAL name terms = Goal(Structure(name, terms))

[<AutoOpen>]
module NUnitExtensions =
    open System

    type MemoryUnit = | Gb | Mb | Kb | B
        with
        member self.calculate (num: int64) =
            let num = float num

            match self with
            | B -> num
            | Kb -> num / 1024.
            | Mb -> num / 1024. / 1024.
            | Gb -> num / 1024. / 1024. / 1024.
        static member SmartCalculate (num: int64) =
            let gbs = Gb.calculate num
            let mbs = Mb.calculate num
            let kbs = Kb.calculate num
            if gbs > 1. then
                sprintf "%f GB" gbs
            elif mbs > 1. then
                sprintf "%f MB" mbs
            elif kbs > 1. then
                sprintf "%f KB" kbs
            else
                sprintf "%d B" num

    type MemoryReportAttribute() =
        inherit TestActionAttribute()
        
        let mutable _timer = Stopwatch()
        let mutable _gcmem = 0L
        let mutable _gc = []
        
        let trackedGcCollections = [0..2]

        override __.Targets = ActionTargets.Test

        override __.BeforeTest test =
            try
                System.AppDomain.MonitoringIsEnabled <- true
            with
            | _ -> ()

            _timer.Start()
            GC.Collect()
            _gcmem <- AppDomain.CurrentDomain.MonitoringTotalAllocatedMemorySize
            // gc executes one or zero times after starting no gc region on a different systems
            _gc <- trackedGcCollections |> List.map (fun i -> GC.CollectionCount(i) + 1)

        override __.AfterTest test = 
            _timer.Stop()
            let gcm = AppDomain.CurrentDomain.MonitoringTotalAllocatedMemorySize
            
            let gcCollects =
                trackedGcCollections
                |> List.map (fun i -> GC.CollectionCount(i))
                |> List.map2 (fun prev cur -> max (cur - prev) 0) _gc
                |> List.fold (fun acc c -> acc + c.ToString() + " ") ""

            let gcResult = sprintf "GC collects: %s Allocated: %s" gcCollects (MemoryUnit.SmartCalculate ((gcm - _gcmem) / 1024L))
            let timeResult = sprintf "Took %f ms" _timer.Elapsed.TotalMilliseconds

            Console.WriteLine(sprintf "***** Test %s. %s. %s." test.FullName timeResult gcResult)

[<TestFixture>]
module ReferenceTests =
    [<Test; MemoryReport>]
    let ``reference test``() =
        [1..100] |> List.iter (fun _ -> [1..10000] |> List.fold (+) 0 |> fun x -> Assert.Greater(x, 0))

[<TestFixture>]
module VariableUnifyTests =
    let getChangeVariableFunction var n =
        function
        | Variable(v) when v = var -> num n
        | v -> VariableTerm(v)

    [<Test; MemoryReport>]
    let ``process struct test``() =
        let changeVariable = getChangeVariableFunction "N" 1.
        VariableUnify.changeVariablesForStruct changeVariable (Structure("test", [var "N1"; var "N"; var "N"]))
        |> check (Structure("test", [var "N1"; num 1.; num 1.]))
        
    [<Test; MemoryReport>]
    let ``post unify params with arguments test3``() =
        VariableUnify.unifyParametersWithArguments (toParams [num 10.; num 5.; var "V"]) (toArgs [num 10.; num 5.; var "V"])
        |> check (Some([num 10.; num 5.; var "V"]))
        VariableUnify.unifyParametersWithArguments (toParams [num 10.; num 5.; var "V"]) (toArgs [var "V"; var "V"; var "V"])
        |> check (Some([num 10.; num 5.; var "V"]))
        VariableUnify.unifyParametersWithArguments (toParams [var "V"; var "V"; var "V"]) (toArgs [num 10.; num 5.; var "V"])
        |> check (Some([num 10.; num 5.; var "V"]))

        VariableUnify.unifyParametersWithArguments (toParams [var "N"]) (toArgs [var "N2"]) |> check (Some([var "N"]))
        VariableUnify.unifyParametersWithArguments (toParams [num 1.]) (toArgs [var "N"]) |> check (Some([num 1.]))
        VariableUnify.unifyParametersWithArguments (toParams [var "N"]) (toArgs [num 1.]) |> check (Some([num 1.]))
        VariableUnify.unifyParametersWithArguments (toParams [num 1.]) (toArgs [num 1.]) |> check (Some([num 1.]))
        VariableUnify.unifyParametersWithArguments (toParams [num 1.]) (toArgs [num 2.]) |> check None

[<TestFixture>]
module SimpleTests =
    open VariableUnify
    open ExpressionUnify

    [<Test; MemoryReport>]
    let testUnifyExpression() = 
        unifyExpression (EqExpr(var "N", num 1.)) (fun (Variable(v)) -> num 1.)
        |> check (EqExpr(num 1., num 1.))
        unifyExpression (EqExpr(var "N", var "N2")) (fun (Variable(v)) -> if v = "N" then num 1. else num 2.)
        |> check (EqExpr(num 1., num 2.))
        unifyExpression (EqExpr(var "N", var "N2")) (fun (Variable(v)) -> if v = "N" then num 1. else var v)
        |> check (EqExpr(num 1., var "N2"))
    
    [<Test; MemoryReport>]
    let testUnifyCalc() =
        unifyExpression (CalcExpr(var "N", Value(num 1.))) (fun (Variable(v)) -> num 2.)
        |> check (CalcExpr(num 2., Value(num 1.)))

        unifyExpression (CalcExpr(var "N", Value(StructureTerm(Structure("+", [var "N"; num 1.]))))) (fun (Variable(v)) -> num 2.)
        |> check (CalcExpr(num 2., Value(StructureTerm(Structure("+", [num 2.; num 1.])))))

    [<Test; MemoryReport>]
    let testUnifyRule() = 
        unifyRule (RULE (SIGNATURE "eq1" [var "N"]) (EqExpr(var "N", num 1.))) (toArgs [num 1.])
        |> check (Some(RULE (SIGNATURE "eq1" [num 1.]) (EqExpr(num 1., num 1.))))
    
    open Execute

    [<Test; MemoryReport>]
    let testExecuteCalc() = 
        executeCalc (Value(num 1.))
        |> check (NumberTerm(1.))

        executeCalc (Plus(Value(num 1.), Value(num 1.)))
        |> check (NumberTerm(2.))
    
    [<Test; MemoryReport>]
    let testExecuteExpression() = 
        let executeCustom a = failwith "unexpected input"
    
        executeExpression (EqExpr(var "N", num 1.)) executeCustom (fun v -> num 1.)
        |> checkExecuteExpression [EqExpr(num 1., num 1.)]
        executeExpression (EqExpr(var "N", num 1.)) executeCustom (fun v -> VariableTerm(v))
        |> checkExecuteExpression [EqExpr(num 1., num 1.)]
        executeExpression (AndExpression(CalcExpr(var "N", Value(num 1.)), EqExpr(var "N", num 1.))) executeCustom (fun v -> num 1.)
        |> checkExecuteExpression [AndExpression(CalcExpr(num 1., Value(num 1.)), EqExpr(num 1., num 1.))]

    open Solve

    [<Test; MemoryReport>]
    let testExecute() = 
        solve (GOAL "eq1" [var "N"]) [RULE (SIGNATURE "eq1" [var "N"]) (EqExpr(var "N", num 1.))]
        |> checkSolve [[num 1.]]

        solve (GOAL "eq2" [num 1.]) [RULE (SIGNATURE "eq2" [var "N"]) (EqExpr(var "N", num 1.))]
        |> checkSolve [[num 1.]]

        solve (GOAL "eq3" [num 2.]) [RULE (SIGNATURE "eq3" [var "N"]) (EqExpr(var "N", num 1.))]
        |> checkSolve []
            
        solve (GOAL "and" [var "N"]) [RULE (SIGNATURE "and" [var "N"]) (AndExpression(EqExpr(var "N", num 1.), EqExpr(var "N", num 2.)))]
        |> checkSolve []

        solve (GOAL "or" [var "N"]) [RULE (SIGNATURE "or" [var "N"]) (OrExpression(EqExpr(var "N", num 1.), EqExpr(var "N", num 2.)))]
        |> checkSolve [[num 1.]; [num 2.]]

        solve (GOAL "fa" [var "N"]) [RULE (SIGNATURE "fa" [var "N"]) (False)]
        |> checkSolve []

        solve (GOAL "innervar" [var "N"]) [RULE (SIGNATURE "innervar" [var "N"]) (AndExpression(EqExpr(var "Temp", num 1.), EqExpr(var "N", var "Temp")))]
        |> checkSolve [[num 1.]]

    [<Test; MemoryReport>]
    let testExecuteStructure() =
        solve (GOAL "structure execute" [num 2.; var "Res"]) [RULE (SIGNATURE "structure execute" [var "N"; var "R"]) (CalcExpr(var "R", Value(StructureTerm(Structure("+", [var "N"; num 1.])))))]
        |> checkSolve [[num 2.; num 3.]]

    [<Test; MemoryReport>]
    let testCut() =
        solve (GOAL "cut" [var "R"]) [RULE (SIGNATURE "cut" [var "R"]) (AndExpression(OrExpression(EqExpr(var "R", num 1.), EqExpr(var "R", num 2.)), Cut))]
        |> checkSolve [[num 1.]]

    [<Test; MemoryReport>]
    let testComplexCut() =
        solve (GOAL "cut" [var "R1"; var "R2"]) [RULE (SIGNATURE "cut" [var "R1"; var "R2"]) (AndExpression(AndExpression(OrExpression(EqExpr(var "R1", num 1.), EqExpr(var "R1", num 2.)), OrExpression(EqExpr(var "R2", num 1.), EqExpr(var "R2", num 2.))), Cut))]
        |> checkSolve [[num 1.; num 1.]]

    [<Test; MemoryReport>]
    let checkLazySolve() =
        solve (GOAL "lazy infinite" [num 1.; var "R"]) [RULE (SIGNATURE "lazy infinite" [var "C"; var "R"]) (OrExpression(EqExpr(var "C", var "R"), AndExpression(CalcExpr(var "NextC", Plus(Value(var "C"), Value(num 1.))), CallExpression(Goal(Structure("lazy infinite", [var "NextC"; var "R"]))))))]
        |> Seq.take 3
        |> checkSolve ([1..3] |> List.map (fun x -> [num 1.; num (float x)]))

    [<Test; MemoryReport>]
    let realTest() =
        solve (GOAL "eq1_both" [var "N"; var "Res"]) [RULE (SIGNATURE "eq1_both" [var "N1"; var "N2"]) (AndExpression((EqExpr(var "N1", num 1.), (EqExpr(var "N2", num 1.)))))]
        |> checkSolve [[num 1.; num 1.]]
        solve(GOAL "eq" [var "N"; var "N2"]) [RULE (SIGNATURE "eq" [var "N1"; var "N2"]) (EqExpr(var "N1", var "N2"))]
        |> checkSolve [[var "N"; var "N"]]

        let oneOrTwoRule = RULE(SIGNATURE "f1" [var "N"; var "Res"]) (OrExpression(AndExpression(EqExpr(var "N", num 1.), EqExpr(var "Res", num 1.)), AndExpression(GrExpr(var "N", num 1.), EqExpr(var "Res", num 2.))))
        solve (GOAL "f1" [num 1.; var "Res"]) [oneOrTwoRule]
        |> checkSolve [[num 1.; num 1.]]
        solve (GOAL "f1" [num 3.; var "Res"]) [oneOrTwoRule]
        |> checkSolve [[num 3.; num 2.]]

        let getN = RULE(SIGNATURE "getn" [var "R"]) (EqExpr(var "R", num 1.))
        let inn = RULE(SIGNATURE "inn" [var "Res"]) (CallExpression(Goal(Structure("getn", [var "Res"]))))
        solve (GOAL "inn" [var "R"]) [getN; inn]
        |> checkSolve [[num 1.]]
        
    [<Test; MemoryReport>]
    let ``test applicative state``() =
        let r0 = RULE (SIGNATURE "F0" [num 1.]) True
        let r1 = RULE (SIGNATURE "F1" [var "X"]) (AndExpression(CallExpression(GOAL "F0" [var "X"]), CallExpression(GOAL "F0" [var "X"])))
        let r2 = RULE (SIGNATURE "F2" [var "X1"]) (AndExpression(CallExpression(GOAL "F1" [var "X1"]), AndExpression(CallExpression(GOAL "F1" [var "X1"]), CallExpression(GOAL "F1" [var "X1"]))))
        solve (GOAL "F2" [var "N"]) [r0; r1; r2]
        |> checkSolve [[num 1.]]

    [<Test; MemoryReport>]
    let ``test factorial rule``() =
        let leftOr = AndExpression(EqExpr(var "N", num 1.), EqExpr(var "Res", num 1.))
        let rightOr = AndExpression(GrExpr(var "N", num 1.), AndExpression(CalcExpr(var "N1", Subsctruct(Value(var "N"), Value(num 1.))), AndExpression(CallExpression(Goal(Structure("factorial", [var "N1"; var "R1"]))), CalcExpr(var "Res", Multiply(Value(var "R1"), Value(var "N"))))))
        let factorial = RULE(SIGNATURE "factorial" [var "N"; var "Res"]) (OrExpression(leftOr, rightOr))

        let knowledgebase = [
            factorial
        ]
        
        let checkf n =
            let rec f x = if x = 1. then 1. else x * f(x - 1.)
            
            solve (GOAL "factorial" [num n; var "Res"]) knowledgebase
            |> checkSolve [[num n; num (f n)]]

        [1..10] |> List.iter (float >> checkf)
        
    [<Test; MemoryReport>]
    let cutFactorialTest() =
        let leftOr = AndExpression(AndExpression(EqExpr(var "N", num 1.), EqExpr(var "Res", num 1.)), Cut)
        let rightOr = AndExpression(CalcExpr(var "N1", Subsctruct(Value(var "N"), Value(num 1.))), AndExpression(CallExpression(Goal(Structure("factorial", [var "N1"; var "R1"]))), CalcExpr(var "Res", Multiply(Value(var "R1"), Value(var "N")))))
        let factorial = RULE(SIGNATURE "factorial" [var "N"; var "Res"]) (OrExpression(leftOr, rightOr))

        let knowledgebase = [
            factorial
        ]
        
        let checkf n =
            let rec f x = if x = 1. then 1. else x * f(x - 1.)
            
            solve (GOAL "factorial" [num n; var "Res"]) knowledgebase
            |> checkSolve [[num n; num (f n)]]

        [1..10] |> List.iter (float >> checkf)

[<TestFixture>]
module RuleTests =
    let person p = RULE(SIGNATURE "person" [stringList p]) True
    let parent p d = RULE(SIGNATURE "parent" [stringList p; stringList d]) True
    let notParent = RULE(SIGNATURE "notParent" [var "P"]) (AndExpression(CallExpression(GOAL "person" [var "P"]), NotExpression(AndExpression(CallExpression(GOAL "person" [var "C"]), CallExpression(GOAL "parent" [var "P"; var "C"])))))
    let grandparent = RULE(SIGNATURE "grandparent" [var "G"; var "D"]) (AndExpression(CallExpression(GOAL "parent" [var "G"; var "P"]), CallExpression(GOAL "parent" [var "P"; var "D"])))

    let knowledgebase = [
        person "Mary";
        person "Polina";
        person "Evgeniy";
        person "Solniwko";
    
        parent "Mary" "Polina";
        parent "Solniwko" "Polina";
        parent "Polina" "Evgeniy";

        grandparent
        notParent
    ]

    [<Test; MemoryReport>]
    let testPersonRule() =
        solve (GOAL "person" [stringList "Polina"]) knowledgebase
        |> checkSolve [[stringList "Polina"]]
        solve (GOAL "person" [var "X"]) knowledgebase
        |> checkSolve [[stringList "Mary"]; [stringList "Polina"]; [stringList "Evgeniy"]; [stringList "Solniwko"]]
        solve (GOAL "person" [stringList "Miwa"]) knowledgebase
        |> checkSolve []

    [<Test; MemoryReport>]
    let testParentRule() =
        solve (GOAL "parent" [stringList "Polina"; var "Descendant"]) knowledgebase
        |> checkSolve [[stringList "Polina"; stringList "Evgeniy"]]
        solve (GOAL "parent" [var "Parent"; var "Descendant"]) knowledgebase
        |> checkSolve [[stringList "Mary"; stringList "Polina"]; [stringList "Solniwko"; stringList "Polina"]; [stringList "Polina"; stringList "Evgeniy"]]
        
    [<Test; MemoryReport>]
    let testParentBidirectRule_person_first() =
        let biparent_pf = RULE(SIGNATURE "biparent_person_first" [var "P"; var "C"]) (AndExpression(CallExpression(GOAL "person" [var "P"]), (AndExpression(CallExpression(GOAL "person" [var "C"]), CallExpression(GOAL "parent" [var "P"; var "C"])))))
        let knowledgebase = knowledgebase@[biparent_pf]
        
        solve (GOAL "biparent_person_first" [var "Parent"; var "Descendant"]) knowledgebase
        |> checkSolve [[stringList "Mary"; stringList "Polina"]; [stringList "Polina"; stringList "Evgeniy"]; [stringList "Solniwko"; stringList "Polina"]]
        
    [<Test; MemoryReport>]
    let testParentBidirectRule_person_last() =
        let biparent_pl = RULE(SIGNATURE "biparent_person_last" [var "P"; var "C"]) (AndExpression(CallExpression(GOAL "parent" [var "P"; var "C"]), AndExpression(CallExpression(GOAL "person" [var "P"]), CallExpression(GOAL "person" [var "C"]))))
        let knowledgebase = knowledgebase@[biparent_pl]
        
        solve (GOAL "biparent_person_last" [var "Parent"; var "Descendant"]) knowledgebase
        |> checkSolve [[stringList "Mary"; stringList "Polina"]; [stringList "Solniwko"; stringList "Polina"]; [stringList "Polina"; stringList "Evgeniy"]]
        
    [<Test; MemoryReport>]
    let testNotParentRule() =
        solve (GOAL "notParent" [var "NotParent"]) knowledgebase
        |> checkSolve [[stringList "Evgeniy"]]

        solve (GOAL "notParent" [stringList "Mary"]) knowledgebase
        |> checkSolve []

    [<Test; MemoryReport>]
    let testGrandparentRule() =
        solve (GOAL "grandparent" [var "GrandParent"; var "Descendant"]) knowledgebase
        |> checkSolve [[stringList "Mary"; stringList "Evgeniy"]; [stringList "Solniwko"; stringList "Evgeniy"]]
        solve (GOAL "grandparent" [stringList "Mary"; stringList "Evgeniy"]) knowledgebase
        |> checkSolve [[stringList "Mary"; stringList "Evgeniy"]]

    //[<Test; MemoryReport>]
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

        let toTest = [1..10000] |> List.map (fun i -> generate (fun p c -> (GOAL "parent" [var p; var c])))

        toTest |> List.map (fun t -> solve t kb |> Seq.toList) |> ignore

[<TestFixture>]
module ListTests =
    open VariableUnify
    open ExpressionUnify
    
    let headRule = RULE (SIGNATURE "head" [var "E"; var "L"]) (EqExpr(ListTerm(TypedListTerm(var "E", VarListTerm(Variable("R")))), var "L"))
    let tailRule = RULE (SIGNATURE "tail" [var "L"; var "T"]) (EqExpr(ListTerm(TypedListTerm(var "E", VarListTerm(Variable("T")))), var "L"))
    let memberRule = RULE (SIGNATURE "member" [var "E"; var "L"]) (OrExpression(CallExpression(GOAL "head" [var "E"; var "L"]), AndExpression(CallExpression(GOAL "tail" [var "L"; var "T"]), CallExpression(GOAL "member" [var "E"; var "T"]))))
    
    let knowledgebase = [headRule; tailRule; memberRule]

    [<Test; MemoryReport>]
    let ``test empty list head``() =
        solve (GOAL "head" [var "E"; stringList ""]) knowledgebase
        |> checkSolve []

    [<Test; MemoryReport>]
    let ``test one element list head``() =
        solve (GOAL "head" [var "E"; stringList "1"]) knowledgebase
        |> checkSolve [[char '1'; stringList "1"]]

    [<Test; MemoryReport>]
    let ``test two elements list head``() =
        solve (GOAL "head" [var "E"; stringList "12"]) knowledgebase
        |> checkSolve [[char '1'; stringList "12"]]

    [<Test; MemoryReport>]
    let ``test empty list tail``() =
        solve (GOAL "tail" [stringList ""; var "T"]) knowledgebase
        |> checkSolve []

    [<Test; MemoryReport>]
    let ``test one element list tail``() =
        solve (GOAL "tail" [stringList "1"; var "T"]) knowledgebase
        |> checkSolve [[stringList "1"; stringList ""]]
        
    [<Test; MemoryReport>]
    let ``test any elements list tail``() =
        solve (GOAL "tail" [stringList "12"; var "T"]) knowledgebase
        |> checkSolve [[stringList "12"; stringList "2"]]
        solve (GOAL "tail" [stringList "123"; var "T"]) knowledgebase
        |> checkSolve [[stringList "123"; stringList "23"]]

    [<Test; MemoryReport>]
    let ``test variable elements list tail``() =
        solve (GOAL "tail" [ListTerm(TypedListTerm(char '1', VarListTerm(Variable("F")))); var "E"]) knowledgebase
        |> checkSolve [[ListTerm(TypedListTerm(char '1', VarListTerm(Variable("F")))); ListTerm(VarListTerm(Variable("F")))]]

    //[<Test; MemoryReport>]
    let ``test empty list member``() =
        solve (GOAL "member" [var "E"; stringList ""]) knowledgebase
        |> checkSolve []

    //[<Test; MemoryReport>]
    let ``test defined list member``() =
        solve (GOAL "member" [var "E"; stringList "123"]) knowledgebase
        |> checkSolve [[var "E"; stringList "1"]; [var "E"; stringList "2"]; [var "E"; stringList "3"]]
    
    //[<Test; MemoryReport>]
    let ``test partly defined list member``() =
        solve (GOAL "member" [var "E"; ListTerm(TypedListTerm(num 1., TypedListTerm(num 2., VarListTerm(Variable("F")))))]) knowledgebase
        |> checkSolve [[var "E"; stringList "1"]; [var "E"; stringList "2"]; [var "E"; stringList "E"]]

    [<Test; MemoryReport>]
    let ``test var list params unification with var list arg``() = 
        unifyParametersWithArguments [Parameter(ListTerm(TypedListTerm(VariableTerm(Variable("Y")), NilTerm)))] [Argument(ListTerm(TypedListTerm(VariableTerm(Variable("Y")), NilTerm)))]
        |> check (Some([ListTerm(TypedListTerm(VariableTerm(Variable("Y")), NilTerm))]))

    [<Test; MemoryReport>]
    let ``test var list rule unification with var list doesn't change inner var``() = 
        unifyRule (RULE (SIGNATURE "eqvarlist" [ListTerm(TypedListTerm(VariableTerm(Variable("Y")), NilTerm))]) True) [Argument(ListTerm(TypedListTerm(VariableTerm(Variable("X")), NilTerm)))]
        |> check (Some(Rule(Signature("eqvarlist", [Parameter(ListTerm(TypedListTerm(VariableTerm(Variable("Y")), NilTerm)))]), True)))

    [<Test; MemoryReport>]
    let ``test var list unification with var list``() =
        solve (GOAL "un" [ListTerm(TypedListTerm(VariableTerm(Variable("X")), NilTerm))]) [RULE(SIGNATURE "un" [ListTerm(TypedListTerm(VariableTerm(Variable("Y")), NilTerm))]) True]
        |> checkSolve [[ListTerm(TypedListTerm(VariableTerm(Variable("X")), NilTerm))]]

open Solve.Parse
open PrologParser

[<TestFixture>]
module ParserTests =
    [<Test; MemoryReport>]
    let checkEmptyListParse() =
        parse "?- list([])."
        |> check (Some(CallParseResult(GOAL "list" [ListTerm(NilTerm)])))
        
    [<Test; MemoryReport>]
    let checkDefinedListParse() =
        parse "?- list([1,2,3])."
        |> check (Some(CallParseResult(GOAL "list" [ListTerm(TypedListTerm(num 1., TypedListTerm(num 2., TypedListTerm(num 3., NilTerm))))])))

    [<Test; MemoryReport>]
    let checkPartlyDefinedListParse() =
        parse "?- list([1 | X])."
        |> check (Some(CallParseResult(GOAL "list" [ListTerm(TypedListTerm(num 1., VarListTerm(Variable("X"))))])))

[<TestFixture>]
module InteractiveTests =
    let interactive = Solve.Interactive()

    [<Test; MemoryReport>]
    let parseFacts() =
        interactive.NewInput "fact(1)." |> check (RuleInfo(RULE(SIGNATURE "fact" [num 1.]) True))
        interactive.NewInput "fact(2)." |> check (RuleInfo(RULE(SIGNATURE "fact" [num 2.]) True))
        interactive.NewInput "fact(X)." |> check (RuleInfo(RULE(SIGNATURE "fact" [var "X"]) True))
        interactive.NewInput "fact(Y)." |> check (RuleInfo(RULE(SIGNATURE "fact" [var "Y"]) True))
        interactive.NewInput "fact(x)." |> check (RuleInfo(RULE(SIGNATURE "fact" [atom "x"]) True))
        interactive.NewInput "fact(y)." |> check (RuleInfo(RULE(SIGNATURE "fact" [atom "y"]) True))

    [<Test; MemoryReport>]
    let parseEqGrLeRule() =
        interactive.NewInput "rule(X) :- X = 1." |> check (RuleInfo(RULE(SIGNATURE "rule" [var "X"]) (EqExpr(var "X", num 1.))))
        interactive.NewInput "rule(X) :- X > 1." |> check (RuleInfo(RULE(SIGNATURE "rule" [var "X"]) (GrExpr(var "X", num 1.))))
        interactive.NewInput "rule(X) :- X < 1." |> check (RuleInfo(RULE(SIGNATURE "rule" [var "X"]) (LeExpr(var "X", num 1.))))
    
    [<Test; MemoryReport>]
    let parseAndRule() =
        interactive.NewInput "rule(X, Y) :- X = 1, Y = 2." |> check (RuleInfo(RULE (SIGNATURE "rule" [var "X"; var "Y"]) (AndExpression(EqExpr(var "X", num 1.), EqExpr(var "Y", num 2.)))))
    
    [<Test; MemoryReport>]
    let parseOrRule() =
        interactive.NewInput "rule(X, Y) :- X = 1 ; Y = 2." |> check (RuleInfo(RULE (SIGNATURE "rule" [var "X"; var "Y"]) (OrExpression(EqExpr(var "X", num 1.), EqExpr(var "Y", num 2.)))))

    [<Test; MemoryReport>]
    let parseFactorialRule() =
        interactive.NewInput "factorial(1,1)." |> check (RuleInfo(RULE(SIGNATURE "factorial" [num 1.; num 1.]) True))

        interactive.NewInput "factorial(X,Y) :- X > 1, X1 is X - 1, factorial(X1, Y1), Y is X * Y1." |> check (RuleInfo(RULE (SIGNATURE "factorial" [var "X"; var "Y"]) (AndExpression(GrExpr(var "X", num 1.), AndExpression(CalcExpr(var "X1", Subsctruct(Value(var "X"), Value(num 1.))), AndExpression(CallExpression(GOAL "factorial" [var "X1"; var "Y1"]), CalcExpr(var "Y", Multiply(Value(var "X"), Value(var "Y1")))))))))
