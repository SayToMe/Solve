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
let inline FACT signature = Rule(signature, True)
[<DebuggerStepThrough>]
let inline GOAL name terms = CallExpression(GoalSignature(name, toArgs terms))

[<TestFixture>]
module ReferenceTests =
    [<Test>]
    let ``reference test``() =
        [1..100] |> List.iter (fun _ -> [1..10000] |> List.fold (+) 0 |> fun x -> Assert.Greater(x, 0))

[<TestFixture>]
module VariableUnifyTests =
    let getChangeVariableFunction var n =
        function
        | Variable(v) when v = var -> num n
        | v -> VariableTerm(v)

    [<Test>]
    let ``process struct test``() =
        let changeVariable = getChangeVariableFunction "N" 1.
        VariableUnify.changeVariablesForStruct changeVariable (Structure("test", [var "N1"; var "N"; var "N"]))
        |> check (Structure("test", [var "N1"; num 1.; num 1.]))
        
    [<Test>]
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

    [<Test>]
    let testUnifyExpression() = 
        unifyExpression (EqExpr(var "N", num 1.)) (fun (Variable(v)) -> num 1.)
        |> check (EqExpr(num 1., num 1.))
        unifyExpression (EqExpr(var "N", var "N2")) (fun (Variable(v)) -> if v = "N" then num 1. else num 2.)
        |> check (EqExpr(num 1., num 2.))
        unifyExpression (EqExpr(var "N", var "N2")) (fun (Variable(v)) -> if v = "N" then num 1. else var v)
        |> check (EqExpr(num 1., var "N2"))
    
    [<Test>]
    let testUnifyCalc() =
        unifyExpression (CalcExpr(var "N", Value(num 1.))) (fun (Variable(v)) -> num 2.)
        |> check (CalcExpr(num 2., Value(num 1.)))

        unifyExpression (CalcExpr(var "N", Value(StructureTerm(Structure("+", [var "N"; num 1.]))))) (fun (Variable(v)) -> num 2.)
        |> check (CalcExpr(num 2., Value(StructureTerm(Structure("+", [num 2.; num 1.])))))

    [<Test>]
    let testUnifyRule() = 
        unifyRule (RULE (SIGNATURE "eq1" [var "N"]) (EqExpr(var "N", num 1.))) (toArgs [num 1.])
        |> check (Some(RULE (SIGNATURE "eq1" [num 1.]) (EqExpr(num 1., num 1.))))
    
    open Execute

    [<Test>]
    let testExecuteCalc() = 
        executeCalc (Value(num 1.))
        |> check (NumberTerm(1.))

        executeCalc (Plus(Value(num 1.), Value(num 1.)))
        |> check (NumberTerm(2.))
    
    [<Test>]
    let testExecuteExpression() = 
        let executeCustom _ = failwith "unexpected input"
    
        executeExpression (EqExpr(var "N", num 1.)) executeCustom (fun v -> num 1.)
        |> checkExecuteExpression [EqExpr(num 1., num 1.)]
        executeExpression (EqExpr(var "N", num 1.)) executeCustom (fun v -> VariableTerm(v))
        |> checkExecuteExpression [EqExpr(num 1., num 1.)]
        executeExpression (AndExpression(CalcExpr(var "N", Value(num 1.)), EqExpr(var "N", num 1.))) executeCustom (fun v -> num 1.)
        |> checkExecuteExpression [AndExpression(CalcExpr(num 1., Value(num 1.)), EqExpr(num 1., num 1.))]

    open Solve
    
    [<Test>]
    let ``test execute var eq to concrete``() = 
        solve (GOAL "eq1" [var "N"]) [RULE (SIGNATURE "eq1" [var "N"]) (EqExpr(var "N", num 1.))]
        |> checkSolve [[Variable "N", num 1.]]

    [<Test>]
    let ``test execute concrete to var eq concrete``() = 
        solve (GOAL "eq2" [num 1.]) [RULE (SIGNATURE "eq2" [var "N"]) (EqExpr(var "N", num 1.))]
        |> checkSolve [[]]

    [<Test>]
    let ``test execute concrete to different concrete``() = 
        solve (GOAL "eq3" [num 2.]) [RULE (SIGNATURE "eq3" [var "N"]) (EqExpr(var "N", num 1.))]
        |> checkSolve []

    [<Test>]
    let ``test execute and eq concrete to wrong concrete``() = 
        solve (GOAL "and" [var "N"]) [RULE (SIGNATURE "and" [var "N"]) (AndExpression(EqExpr(var "N", num 1.), EqExpr(var "N", num 2.)))]
        |> checkSolve []
        
    [<Test>]
    let ``test execute or eq var to concrete``() = 
        solve (GOAL "or" [var "N"]) [RULE (SIGNATURE "or" [var "N"]) (OrExpression(EqExpr(var "N", num 1.), EqExpr(var "N", num 2.)))]
        |> checkSolve [[Variable "N", num 1.]; [Variable "N", num 2.]]

    [<Test>]
    let ``test execute fail fact``() = 
        solve (GOAL "fa" [var "N"]) [RULE (SIGNATURE "fa" [var "N"]) (False)]
        |> checkSolve []

    [<Test>]
    let ``test execute inner variable eq``() = 
        solve (GOAL "innervar" [var "N"]) [RULE (SIGNATURE "innervar" [var "N"]) (AndExpression(EqExpr(var "Temp", num 1.), EqExpr(var "N", var "Temp")))]
        |> checkSolve [[Variable "N", num 1.]]

    [<Test>]
    let testExecuteStructure() =
        solve (GOAL "structure execute" [num 2.; var "Res"]) [RULE (SIGNATURE "structure execute" [var "N"; var "R"]) (CalcExpr(var "R", Value(StructureTerm(Structure("+", [var "N"; num 1.])))))]
        |> checkSolve [[Variable "Res", num 3.]]

    [<Test>]
    let testCut() =
        solve (GOAL "cut" [var "R"]) [RULE (SIGNATURE "cut" [var "R"]) (AndExpression(OrExpression(EqExpr(var "R", num 1.), EqExpr(var "R", num 2.)), Cut))]
        |> checkSolve [[Variable "R", num 1.]]

    [<Test>]
    let testComplexCut() =
        solve (GOAL "cut" [var "R1"; var "R2"]) [RULE (SIGNATURE "cut" [var "R1"; var "R2"]) (AndExpression(AndExpression(OrExpression(EqExpr(var "R1", num 1.), EqExpr(var "R1", num 2.)), OrExpression(EqExpr(var "R2", num 1.), EqExpr(var "R2", num 2.))), Cut))]
        |> checkSolve [[Variable "R1", num 1.; Variable "R2", num 1.]]

    [<Test>]
    let checkLazySolve() =
        solve (GOAL "lazy infinite" [num 1.; var "R"]) [RULE (SIGNATURE "lazy infinite" [var "C"; var "R"]) (OrExpression(EqExpr(var "C", var "R"), AndExpression(CalcExpr(var "NextC", Plus(Value(var "C"), Value(num 1.))), GOAL "lazy infinite" [var "NextC"; var "R"])))]
        |> Seq.take 3
        |> checkSolve ([1..3] |> List.map (fun x -> [Variable "R", num (float x)]))
        
    [<Test>]
    let ``test eq variables to concrete``() =
        solve (GOAL "eq1_both" [var "N"; var "Res"]) [RULE (SIGNATURE "eq1_both" [var "N1"; var "N2"]) (AndExpression((EqExpr(var "N1", num 1.), (EqExpr(var "N2", num 1.)))))]
        |> checkSolve [[Variable "N", num 1.; Variable "Res", num 1.]]
        
    [<Test>]
    let ``test eq variables to variable``() =
        solve(GOAL "eq" [var "N"; var "N2"]) [RULE (SIGNATURE "eq" [var "N1"; var "N2"]) (EqExpr(var "N1", var "N2"))]
        |> checkSolve [[Variable "N", var "N2"]]
        
    [<Test>]
    let ``test eq variables in or expression``() =
        let oneOrTwoRule = RULE(SIGNATURE "f1" [var "N"; var "Res"]) (OrExpression(AndExpression(EqExpr(var "N", num 1.), EqExpr(var "Res", num 1.)), AndExpression(GrExpr(var "N", num 1.), EqExpr(var "Res", num 2.))))
        solve (GOAL "f1" [num 1.; var "Res"]) [oneOrTwoRule]
        |> checkSolve [[Variable "Res", num 1.]]
        solve (GOAL "f1" [num 3.; var "Res"]) [oneOrTwoRule]
        |> checkSolve [[Variable "Res", num 2.]]

    [<Test>]
    let ``test nested variables eq``() =
        let getN = RULE(SIGNATURE "getn" [var "R"]) (EqExpr(var "R", num 1.))
        let inn = RULE(SIGNATURE "inn" [var "Res"]) (CallExpression(GoalSignature("getn", toArgs [var "Res"])))
        solve (GOAL "inn" [var "R"]) [getN; inn]
        |> checkSolve [[Variable "R", num 1.]]
        
    [<Test>]
    let ``test applicative state``() =
        let r0 = RULE (SIGNATURE "F0" [num 1.]) True
        let r1 = RULE (SIGNATURE "F1" [var "X"]) (AndExpression(GOAL "F0" [var "X"], GOAL "F0" [var "X"]))
        let r2 = RULE (SIGNATURE "F2" [var "X1"]) (AndExpression(GOAL "F1" [var "X1"], AndExpression(GOAL "F1" [var "X1"], GOAL "F1" [var "X1"])))
        solve (GOAL "F2" [var "N"]) [r0; r1; r2]
        |> checkSolve [[Variable "N", num 1.]]

    [<Test>]
    let ``test factorial rule``() =
        let leftOr = AndExpression(EqExpr(var "N", num 1.), EqExpr(var "Res", num 1.))
        let rightOr = AndExpression(GrExpr(var "N", num 1.), AndExpression(CalcExpr(var "N1", Subsctruct(Value(var "N"), Value(num 1.))), AndExpression(GOAL "factorial" [var "N1"; var "R1"], CalcExpr(var "Res", Multiply(Value(var "R1"), Value(var "N"))))))
        let factorial = RULE(SIGNATURE "factorial" [var "N"; var "Res"]) (OrExpression(leftOr, rightOr))

        let knowledgebase = [
            factorial
        ]
        
        let checkf n =
            let rec f x = if x = 1. then 1. else x * f(x - 1.)
            
            solve (GOAL "factorial" [num n; var "Res"]) knowledgebase
            |> checkSolve [[Variable "Res",  num (f n)]]

        [1..10] |> List.iter (float >> checkf)
        
    [<Test>]
    let cutFactorialTest() =
        let leftOr = AndExpression(AndExpression(EqExpr(var "N", num 1.), EqExpr(var "Res", num 1.)), Cut)
        let rightOr = AndExpression(CalcExpr(var "N1", Subsctruct(Value(var "N"), Value(num 1.))), AndExpression(GOAL "factorial" [var "N1"; var "R1"], CalcExpr(var "Res", Multiply(Value(var "R1"), Value(var "N")))))
        let factorial = RULE(SIGNATURE "factorial" [var "N"; var "Res"]) (OrExpression(leftOr, rightOr))

        let knowledgebase = [
            factorial
        ]
        
        let checkf n =
            let rec f x = if x = 1. then 1. else x * f(x - 1.)
            
            solve (GOAL "factorial" [num n; var "Res"]) knowledgebase
            |> checkSolve [[Variable "Res", num (f n)]]

        [1..10] |> List.iter (float >> checkf)

[<TestFixture>]
module RuleTests =
    let person p = RULE(SIGNATURE "person" [stringList p]) True
    let parent p d = RULE(SIGNATURE "parent" [stringList p; stringList d]) True
    let notParent = RULE(SIGNATURE "notParent" [var "P"]) (AndExpression(GOAL "person" [var "P"], NotExpression(AndExpression(GOAL "person" [var "C"], GOAL "parent" [var "P"; var "C"]))))
    let grandparent = RULE(SIGNATURE "grandparent" [var "G"; var "D"]) (AndExpression(GOAL "parent" [var "G"; var "P"], GOAL "parent" [var "P"; var "D"]))

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
    
    [<Test>]
    let ``test defined exist person rule``() =
        solve (GOAL "person" [stringList "Polina"]) knowledgebase
        |> checkSolve [[]]
        
    [<Test>]
    let ``test defined absent person rule``() =
        solve (GOAL "person" [stringList "Miwa"]) knowledgebase
        |> checkSolve []
        
    [<Test>]
    let ``test all persons rule``() =
        solve (GOAL "person" [var "X"]) knowledgebase
        |> checkSolve [[Variable "X", stringList "Mary"]; [Variable "X", stringList "Polina"]; [Variable "X", stringList "Evgeniy"]; [Variable "X", stringList "Solniwko"]]

    [<Test>]
    let testParentRule() =
        solve (GOAL "parent" [stringList "Polina"; var "Descendant"]) knowledgebase
        |> checkSolve [[Variable "Descendant",  stringList "Evgeniy"]]
        solve (GOAL "parent" [var "Parent"; var "Descendant"]) knowledgebase
        |> checkSolve [[Variable "Parent", stringList "Mary"; Variable "Descendant", stringList "Polina"]; [Variable "Parent", stringList "Solniwko"; Variable "Descendant", stringList "Polina"]; [Variable "Parent", stringList "Polina"; Variable "Descendant", stringList "Evgeniy"]]
        
    [<Test>]
    let testParentBidirectRule_person_first() =
        let biparent_pf = RULE(SIGNATURE "biparent_person_first" [var "P"; var "C"]) (AndExpression(GOAL "person" [var "P"], (AndExpression(GOAL "person" [var "C"], GOAL "parent" [var "P"; var "C"]))))
        let knowledgebase = knowledgebase@[biparent_pf]
        
        solve (GOAL "biparent_person_first" [var "Parent"; var "Descendant"]) knowledgebase
        |> checkSolve [[Variable "Parent", stringList "Mary"; Variable "Descendant", stringList "Polina"]; [Variable "Parent", stringList "Polina"; Variable "Descendant", stringList "Evgeniy"]; [Variable "Parent", stringList "Solniwko"; Variable "Descendant", stringList "Polina"]]
        
    [<Test>]
    let testParentBidirectRule_person_last() =
        let biparent_pl = RULE(SIGNATURE "biparent_person_last" [var "P"; var "C"]) (AndExpression(GOAL "parent" [var "P"; var "C"], AndExpression(GOAL "person" [var "P"], GOAL "person" [var "C"])))
        let knowledgebase = knowledgebase@[biparent_pl]
        
        solve (GOAL "biparent_person_last" [var "Parent"; var "Descendant"]) knowledgebase
        |> checkSolve [[Variable "Parent", stringList "Mary"; Variable "Descendant", stringList "Polina"]; [Variable "Parent", stringList "Solniwko"; Variable "Descendant", stringList "Polina"]; [Variable "Parent", stringList "Polina"; Variable "Descendant", stringList "Evgeniy"]]
        
    [<Test>]
    let testNotParentRule() =
        solve (GOAL "notParent" [var "NotParent"]) knowledgebase
        |> checkSolve [[Variable "NotParent", stringList "Evgeniy"]]

        solve (GOAL "notParent" [stringList "Mary"]) knowledgebase
        |> checkSolve []

    [<Test>]
    let testGrandparentRule() =
        solve (GOAL "grandparent" [var "GrandParent"; var "Descendant"]) knowledgebase
        |> checkSolve [[Variable "GrandParent", stringList "Mary"; Variable "Descendant", stringList "Evgeniy"]; [Variable "GrandParent", stringList "Solniwko"; Variable "Descendant", stringList "Evgeniy"]]
        solve (GOAL "grandparent" [stringList "Mary"; stringList "Evgeniy"]) knowledgebase
        |> checkSolve [[]]

    //[<Test>]
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
    let tailRule = RULE (SIGNATURE "tail" [var "L"; var "T"]) (AndExpression(EqExpr(ListTerm(TypedListTerm(var "E", VarListTerm(Variable("T")))), var "L"), NotExpression(EqExpr(var "L", var "T"))))
    let memberRule = RULE (SIGNATURE "member" [var "E"; var "L"]) (OrExpression(GOAL "head" [var "E"; var "L"], AndExpression(GOAL "tail" [var "L"; var "T"], GOAL "member" [var "E"; var "T"])))
    
    let knowledgebase = [headRule; tailRule; memberRule]

    [<Test>]
    let ``test empty list head``() =
        solve (GOAL "head" [var "E"; stringList ""]) knowledgebase
        |> checkSolve []

    [<Test>]
    let ``test one element list head``() =
        solve (GOAL "head" [var "E"; stringList "1"]) knowledgebase
        |> checkSolve [[Variable "E", char '1']]

    [<Test>]
    let ``test two elements list head``() =
        solve (GOAL "head" [var "E"; stringList "12"]) knowledgebase
        |> checkSolve [[Variable "E", char '1']]

    [<Test>]
    let ``test empty list tail``() =
        solve (GOAL "tail" [stringList ""; var "T"]) knowledgebase
        |> checkSolve []

    [<Test>]
    let ``test one element list tail``() =
        solve (GOAL "tail" [stringList "1"; var "T"]) knowledgebase
        |> checkSolve [[Variable "T", stringList ""]]
        
    [<Test>]
    let ``test any elements list tail``() =
        solve (GOAL "tail" [stringList "12"; var "T"]) knowledgebase
        |> checkSolve [[Variable "T", stringList "2"]]
        solve (GOAL "tail" [stringList "123"; var "T"]) knowledgebase
        |> checkSolve [[Variable "T", stringList "23"]]

    [<Test>]
    let ``test variable elements list tail cant being unified``() =
        solve (GOAL "tail" [ListTerm(TypedListTerm(char '1', VarListTerm(Variable("F")))); var "E"]) knowledgebase
        |> checkSolve []

    [<Test>]
    let ``test empty list member``() =
        solve (GOAL "member" [var "E"; stringList ""]) knowledgebase
        |> checkSolve []

    [<Test>]
    let ``test defined list member``() =
        solve (GOAL "member" [var "E"; stringList "123"]) knowledgebase
        |> checkSolve [[Variable "E", char '1']; [Variable "E", char '2']; [Variable "E", char '3']]
    
    [<Test>]
    let ``test partly defined list member of one``() =
        solve (GOAL "member" [var "E"; ListTerm(TypedListTerm(num 1., VarListTerm(Variable("F"))))]) knowledgebase
        |> checkSolve [[Variable "E", num 1.]]

    [<Test>]
    let ``test partly defined list member of two``() =
        solve (GOAL "member" [var "E"; ListTerm(TypedListTerm(num 1., TypedListTerm(num 2., VarListTerm(Variable("F")))))]) knowledgebase
        |> checkSolve [[Variable "E", num 1.]; [Variable "E", num 2.]]

    [<Test>]
    let ``test var list params unification with var list arg``() = 
        unifyParametersWithArguments [Parameter(ListTerm(TypedListTerm(VariableTerm(Variable("Y")), NilTerm)))] [Argument(ListTerm(TypedListTerm(VariableTerm(Variable("Y")), NilTerm)))]
        |> check (Some([ListTerm(TypedListTerm(VariableTerm(Variable("Y")), NilTerm))]))

    [<Test>]
    let ``test var list rule unification with var list doesn't change inner var``() = 
        unifyRule (RULE (SIGNATURE "eqvarlist" [ListTerm(TypedListTerm(VariableTerm(Variable("Y")), NilTerm))]) True) [Argument(ListTerm(TypedListTerm(VariableTerm(Variable("X")), NilTerm)))]
        |> check (Some(Rule(Signature("eqvarlist", [Parameter(ListTerm(TypedListTerm(VariableTerm(Variable("Y")), NilTerm)))]), True)))

    [<Test>]
    let ``test var list unification with var list``() =
        solve (GOAL "un" [ListTerm(TypedListTerm(VariableTerm(Variable("X")), NilTerm))]) [RULE(SIGNATURE "un" [ListTerm(TypedListTerm(VariableTerm(Variable("Y")), NilTerm))]) True]
        |> checkSolve [[]]


[<TestFixture>]
module ListTestsParsed =
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
    
        member __.KB = kb
        member __.Output = output
    
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
    
    let headRule = RULE (SIGNATURE "head" [var "E"; var "L"]) (EqExpr(ListTerm(TypedListTerm(var "E", VarListTerm(Variable("R")))), var "L"))
    let tailRule = RULE (SIGNATURE "tail" [var "L"; var "T"]) (AndExpression(EqExpr(ListTerm(TypedListTerm(var "E", VarListTerm(Variable("T")))), var "L"), NotExpression(EqExpr(var "L", var "T"))))
    let memberRule = RULE (SIGNATURE "member" [var "E"; var "L"]) (OrExpression(GOAL "head" [var "E"; var "L"], AndExpression(GOAL "tail" [var "L"; var "T"], GOAL "member" [var "E"; var "T"])))
    
    let knowledgebase = [headRule; tailRule; memberRule]

    [<Test>]
    let ``Check facts test``() =
        TestTerminal()
        |>> "test(1)."
        |>> "test(2)."
        |?> "test(X)."
        |> expectedResult [[(Variable "X", num 1.)]; [(Variable "X", num 2.)]]
        
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
        
    [<Test>]
    let ``Check head on list test``() =
        TestTerminal()
        |> insertHeadRule
        |?> "head(X, [1, 2, 3])."
        |> expectedResult [[(Variable "X", num 1.)]]
        
    [<Test>]
    let ``Check tail on empty list test``() =
        TestTerminal()
        |> insertTailRule
        |?> "tail(X, [])."
        |> expectedResult []
        
    [<Test>]
    let ``Check tail on single element list test``() =
        TestTerminal()
        |> insertTailRule
        |?> "tail(X, [1])."
        |> expectedResult [[(Variable "X", numList [])]]
        
    [<Test>]
    let ``Check tail on list test``() =
        TestTerminal()
        |> insertTailRule
        |?> "tail(X, [1, 2, 3])."
        |> expectedResult [[(Variable "X", numList [2.; 3.])]]