namespace Solve.Tests
open NUnit.Framework

open Solve

open TermTypes
open TermTypes.Transformers

open Rule

open Solve.Tests.Common

open Solve

[<TestFixture>]
module ListTests =
    let headRule = RULE (SIGNATURE "head" [var "E"; var "L"]) (EqExpr(ListTerm(TypedListTerm(var "E", VarListTerm(Variable("R")))), var "L"))
    let tailRule = RULE (SIGNATURE "tail" [var "L"; var "T"]) (AndExpression(EqExpr(ListTerm(TypedListTerm(var "E", VarListTerm(Variable("T")))), var "L"), NotExpression(EqExpr(var "L", var "T"))))
    let memberRule = RULE (SIGNATURE "member" [var "E"; var "L"]) (OrExpression(GOAL "head" [var "E"; var "L"], AndExpression(GOAL "tail" [var "L"; var "T"], GOAL "member" [var "E"; var "T"])))
    let knowledgebase = [headRule; tailRule; memberRule]

    [<Test>]
    let ``Given `list module` solve with head(E, []) should return false``() =
        solve (GOAL "head" [var "E"; stringList ""]) knowledgebase
        |> checkSolve []

    [<Test>]
    let ``Given `list module` solve with head(E, ['1']) should return [E = '1']``() =
        solve (GOAL "head" [var "E"; stringList "1"]) knowledgebase
        |> checkSolve [[Variable "E", char '1']]

    [<Test>]
    let ``Given `list module` solve with head(E, ['1', '2']) should return [E = '1']``() =
        solve (GOAL "head" [var "E"; stringList "12"]) knowledgebase
        |> checkSolve [[Variable "E", char '1']]

    [<Test>]
    let ``Given `list module` solve with tail([], T) should return false``() =
        solve (GOAL "tail" [stringList ""; var "T"]) knowledgebase
        |> checkSolve []

    [<Test>]
    let ``Given `list module` solve with tail(['1'], T) should return [T = []]``() =
        solve (GOAL "tail" [stringList "1"; var "T"]) knowledgebase
        |> checkSolve [[Variable "T", stringList ""]]

    [<Test>]
    let ``Given `list module` solve with tail(['1', '2'], T) should return [T = ['2']]``() =
        solve (GOAL "tail" [stringList "12"; var "T"]) knowledgebase
        |> checkSolve [[Variable "T", stringList "2"]]
        solve (GOAL "tail" [stringList "123"; var "T"]) knowledgebase
        |> checkSolve [[Variable "T", stringList "23"]]

    [<Test>]
    let ``Given `list module` solve with tail(['1' | F], E) should return false``() =
        solve (GOAL "tail" [ListTerm(TypedListTerm(char '1', VarListTerm(Variable("F")))); var "E"]) knowledgebase
        |> checkSolve []

    [<Test>]
    let ``Given `list module` solve with member(E, []) should return false``() =
        solve (GOAL "member" [var "E"; stringList ""]) knowledgebase
        |> checkSolve []

    [<Test>]
    let ``Given `list module` solve with member(E, ['1', '2', '3']) should return [E = '1'], [E = '2'], [E = '3']``() =
        solve (GOAL "member" [var "E"; stringList "123"]) knowledgebase
        |> checkSolve [[Variable "E", char '1']; [Variable "E", char '2']; [Variable "E", char '3']]
    
    [<Test>]
    let ``Given `list module` solve with member(E, [1 | F]) should return [E = 1]``() =
        solve (GOAL "member" [var "E"; ListTerm(TypedListTerm(num 1., VarListTerm(Variable("F"))))]) knowledgebase
        |> checkSolve [[Variable "E", num 1.]]

    [<Test>]
    let ``Given `list module` solve with member(E, [1, 2 | F]) should return [E = 1], [E = 2]``() =
        solve (GOAL "member" [var "E"; ListTerm(TypedListTerm(num 1., TypedListTerm(num 2., VarListTerm(Variable("F")))))]) knowledgebase
        |> checkSolve [[Variable "E", num 1.]; [Variable "E", num 2.]]

    [<Test>]
    let ``Given `un([[] | Y]):- true.` solve with un([[] | X]) should return true``() =
        solve (GOAL "un" [ListTerm(TypedListTerm(VariableTerm(Variable("X")), NilTerm))]) [RULE(SIGNATURE "un" [ListTerm(TypedListTerm(VariableTerm(Variable("Y")), NilTerm))]) True]
        |> checkSolve [[]]
