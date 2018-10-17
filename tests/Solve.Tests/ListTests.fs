namespace Solve.Tests
open System
open NUnit.Framework

open NUnit.Framework
open System.Diagnostics

open Solve

open TermTypes
open TermTypes.Transformers

open Rule
open Rule.Transformers

open Solve.Tests.Common

open Solve

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
