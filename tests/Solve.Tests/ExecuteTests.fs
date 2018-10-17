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

[<TestFixture>]
module ExecuteTests =
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
