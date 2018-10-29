namespace Solve.Tests
open NUnit.Framework

open Solve

open TermTypes
open TermTypes.Transformers

open Rule

open Solve.Tests.Common

[<TestFixture>]
module ExecuteTests =
    open Execute
    let executeCustomFailFn _ = failwith "unexpected input"

    [<Test>]
    let ``Given (1) when execute calculation should return 1``() = 
        executeCalc (Value(num 1.))
        |> check (NumberTerm(1.))

    [<Test>]
    let ``Given (1 + 1) when execute calculation should return 2``() = 
        executeCalc (Plus(Value(num 1.), Value(num 1.)))
        |> check (NumberTerm(2.))
    
    [<Test>]
    let ``Given (V -> 1) with (Eq(N, 1)) should return (Eq(1, 1))``() = 
        executeExpression (EqExpr(var "N", num 1.)) executeCustomFailFn (fun v -> num 1.)
        |> checkExecuteExpression [EqExpr(num 1., num 1.)]
    
    [<Test>]
    let ``Given (N -> N) with (Eq(N, 1)) should return (Eq(1, 1))``() = 
        executeExpression (EqExpr(var "N", num 1.)) executeCustomFailFn (fun v -> VariableTerm(v))
        |> checkExecuteExpression [EqExpr(num 1., num 1.)]
    
    [<Test>]
    let ``Given (N -> 1) with (Eq(N, 1), Eq(N, 1)) should return (Eq(1, 1), Eq(1, 1))``() = 
        executeExpression (AndExpression(CalcExpr(var "N", Value(num 1.)), EqExpr(var "N", num 1.))) executeCustomFailFn (fun v -> num 1.)
        |> checkExecuteExpression [AndExpression(CalcExpr(num 1., Value(num 1.)), EqExpr(num 1., num 1.))]
