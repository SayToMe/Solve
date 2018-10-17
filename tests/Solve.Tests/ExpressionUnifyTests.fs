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
module ExpressionUnifyTests =
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

    [<Test>]
    let ``Given eq(X, X) call with eq(1, X) should return eq(1, 1)``() = 
        unifyRule (RULE (SIGNATURE "eq" [var "X"; var "X"]) True) (toArgs [num 1.; var "X"])
        |> check (Some(RULE (SIGNATURE "eq" [num 1.; num 1.]) True))

    [<Test>]
    let ``Given eq(X, X) call with eq(X, 1) should return eq(1, 1)``() = 
        unifyRule (RULE (SIGNATURE "eq" [var "X"; var "X"]) True) (toArgs [var "X"; num 1.])
        |> check (Some(RULE (SIGNATURE "eq" [num 1.; num 1.]) True))

    [<Test>]
    let ``Given eq(X, X) call with eq(1, 2) should return None``() = 
        unifyRule (RULE (SIGNATURE "eq" [var "X"; var "X"]) True) (toArgs [num 1.; num 2.])
        |> check None

    [<Test>]
    let ``Given (X, X) parameters and (1, 2) arguments unify should return None``() =
        unifyParametersWithArguments (toParams [var "X"; var "X"]) (toArgs [num 1.; num 2.])
        |> check None

    [<Test>]
    let ``Given eq(X, X) call with eq([1, 2], [1, X]) should return eq([1, 2], [1, 2])``() = 
        unifyRule (RULE (SIGNATURE "eq" [var "X"; var "X"]) True) (toArgs [numList [1.; 2.]; ListTerm(TypedListTerm(num 1., TypedListTerm(var "X", NilTerm)))])
        |> check (Some(RULE (SIGNATURE "eq" [numList [1.; 2.]; numList [1.; 2.]]) True))
        
    [<Test>]
    let ``Given head(X, [X | T]) call with head(X, [1, 2]) should return head(1, [1, 2])``() = 
        unifyRule (RULE (SIGNATURE "head" [var "X"; ListTerm(TypedListTerm(var "X", VarListTerm(Variable "T")))]) True) (toArgs [var "X"; numList [1.; 2.]])
        |> check (Some(RULE (SIGNATURE "head" [num 1.; numList [1.; 2.]]) True))

    [<Test>]
    let ``Given head([X | T], X) call with head([1, 2], X) should return head([1, 2], 1)``() = 
        unifyRule (RULE (SIGNATURE "head" [ListTerm(TypedListTerm(var "X", VarListTerm(Variable "T"))); var "X"]) True) (toArgs [numList [1.; 2.]; var "X"])
        |> check (Some(RULE (SIGNATURE "head" [numList [1.; 2.]; num 1.]) True))
