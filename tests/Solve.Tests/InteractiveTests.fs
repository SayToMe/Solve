module Solve.InteractiveTests

open Solve.Tests

open NUnit.Framework
open System.Diagnostics

open Solve
open Solve.TermTypes

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

        interactive.NewInput "factorial(X,Y) :- X > 1, X1 is X - 1, factorial(X1, Y1), Y is X * Y1." |> check (RuleInfo(RULE (SIGNATURE "factorial" [var "X"; var "Y"]) (AndExpression(GrExpr(var "X", num 1.), AndExpression(CalcExpr(var "X1", Subsctruct(Value(var "X"), Value(num 1.))), AndExpression(GOAL "factorial" [var "X1"; var "Y1"], CalcExpr(var "Y", Multiply(Value(var "X"), Value(var "Y1")))))))))
