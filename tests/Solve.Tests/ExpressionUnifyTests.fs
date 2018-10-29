namespace Solve.Tests
open NUnit.Framework

open Solve

open TermTypes
open TermTypes.Transformers

open Rule

open Solve.Tests.Common

[<TestFixture>]
module ExpressionUnifyTests =
    open ExpressionUnify

    [<Test>]
    let ``Given (N -> 1) when unify `N is 1` should return `1 is 1` ``() = 
        unifyExpression (EqExpr(var "N", num 1.)) (fun (Variable(v)) -> num 1.)
        |> check (EqExpr(num 1., num 1.))

    [<Test>]
    let ``Given (N -> 1, N2 -> 2) when unify `N is N2` should return `1 is 2` ``() = 
        unifyExpression (EqExpr(var "N", var "N2")) (fun (Variable(v)) -> if v = "N" then num 1. else num 2.)
        |> check (EqExpr(num 1., num 2.))

    [<Test>]
    let ``Given (N -> 1, N2 -> N2) when unify `N = N2` should return `1 = N2` ``() = 
        unifyExpression (EqExpr(var "N", var "N2")) (fun (Variable(v)) -> if v = "N" then num 1. else var v)
        |> check (EqExpr(num 1., var "N2"))
    
    [<Test>]
    let ``Given (N -> 2) when unify `N is 1` should return `2 is 1` ``() =
        unifyExpression (CalcExpr(var "N", Value(num 1.))) (fun (Variable(v)) -> num 2.)
        |> check (CalcExpr(num 2., Value(num 1.)))

    [<Test>]
    let ``Given (N -> 2) when unify `N is N + 1` should return `2 is 2 + 1` ``() =
        unifyExpression (CalcExpr(var "N", Value(StructureTerm(Structure("+", [var "N"; num 1.]))))) (fun (Variable(v)) -> num 2.)
        |> check (CalcExpr(num 2., Value(StructureTerm(Structure("+", [num 2.; num 1.])))))
