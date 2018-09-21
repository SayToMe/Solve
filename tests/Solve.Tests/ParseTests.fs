﻿module Solve.InteractiveTests

open Solve.Tests

open NUnit.Framework

open Solve.TermTypes
open Solve.TermTypes.Transformers
open Solve.Rule
open Solve.Rule.Transformers

open FParsec

open Solve.PrologParser
open Solve.PrologParser.Primitives
open Solve.PrologParser.Parser

open Solve.PrimitivesTests

[<TestFixture>]
module ParserTests =
    let checkParseFailure given =
        match given with
        | ParseError _ -> ()
        | _ -> failwithf "Expected failure but was %A" given

    [<Test>]
    let parsePlAssertOfFactWithNonEmptySignature() = parsePlString ":-a(1)." |> check (RuleParseResult(FACT <| SIGNATURE "a" [num 1.]))
    
    [<Test>]
    let parsePlQueryForNonEmptySignature() = parsePlString "?-a(1)." |> check (CallParseResult(GOAL "a" [num 1.]))
    
    [<Test>]
    let checkNoParamsFactParse() =
        parse ":-fact()."
        |> check (RuleParseResult(FACT <| SIGNATURE "fact" []))
    
    [<Test>]
    let checkNumberParamFactParse() =
        parse ":-fact(1)."
        |> check (RuleParseResult(FACT <| SIGNATURE  "fact" [num 1.]))
    
    [<Test>]
    let checkAtomParamFactParse() =
        parse ":-fact(a)."
        |> check (RuleParseResult(FACT <| SIGNATURE  "fact" [atom "a"]))
    
    [<Test>]
    let checkEmptyListParse() =
        parse "?-list([])."
        |> check (CallParseResult(GOAL "list" [ListTerm(NilTerm)]))
    
    [<Test>]
    let checkDefinedListParse() =
        parse "?-list([1,2,3])."
        |> check (CallParseResult(GOAL "list" [ListTerm(TypedListTerm(num 1., TypedListTerm(num 2., TypedListTerm(num 3., NilTerm))))]))
    
    [<Test>]
    let checkPartlyDefinedListParse() =
        parse "?-list([1|X])."
        |> check (CallParseResult(GOAL "list" [ListTerm(TypedListTerm(num 1., VarListTerm(Variable("X"))))]))

    [<Test>]
    let checkFailQuery() =
        parse "?-lli(()."
        |> checkParseFailure
    
    [<Test>]
    let parseFacts() =
         parse ":-fact(1)." |> check (RuleParseResult(RULE(SIGNATURE "fact" [num 1.]) True))
         parse ":-fact(2)." |> check (RuleParseResult(RULE(SIGNATURE "fact" [num 2.]) True))
         parse ":-fact(X)." |> check (RuleParseResult(RULE(SIGNATURE "fact" [var "X"]) True))
         parse ":-fact(Y)." |> check (RuleParseResult(RULE(SIGNATURE "fact" [var "Y"]) True))
         parse ":-fact(x)." |> check (RuleParseResult(RULE(SIGNATURE "fact" [atom "x"]) True))
         parse ":-fact(y)." |> check (RuleParseResult(RULE(SIGNATURE "fact" [atom "y"]) True))

    [<Test>]
    let parseFactWithoutDot() =
        parse ":- fact(y)" |> checkParseFailure

    [<Test>]
    let parseFactWithInitialSpace() =
        parse ":- fact(y)." |> check (RuleParseResult(RULE(SIGNATURE "fact" [atom "y"]) True))

    [<Test>]
    let parseFactWithTrailingSpace() =
        parse ":- fact(y). " |> check (RuleParseResult(RULE(SIGNATURE "fact" [atom "y"]) True))

    [<Test>]
    let parseFactWithSpaceBeforeDot() =
        parse ":- fact(y) . " |> check (RuleParseResult(RULE(SIGNATURE "fact" [atom "y"]) True))

    [<Test>]
    let parseEqGrLeRuleWithoutSpaces() =
        parse ":-rule(X):-X=1." |> check (RuleParseResult(RULE(SIGNATURE "rule" [var "X"]) (EqExpr(var "X", num 1.))))
        parse ":-rule(X):-X>1." |> check (RuleParseResult(RULE(SIGNATURE "rule" [var "X"]) (GrExpr(var "X", num 1.))))
        parse ":-rule(X):-X<1." |> check (RuleParseResult(RULE(SIGNATURE "rule" [var "X"]) (LeExpr(var "X", num 1.))))

    [<Test>]
    let parseEqGrLeRuleWithSpaces() =
        parse ":-rule(X) :- X = 1." |> check (RuleParseResult(RULE(SIGNATURE "rule" [var "X"]) (EqExpr(var "X", num 1.))))
        parse ":-rule(X) :- X > 1." |> check (RuleParseResult(RULE(SIGNATURE "rule" [var "X"]) (GrExpr(var "X", num 1.))))
        parse ":-rule(X) :- X < 1." |> check (RuleParseResult(RULE(SIGNATURE "rule" [var "X"]) (LeExpr(var "X", num 1.))))

    [<Test>]
    let parseEqGrLeRuleWithOnlyExprSpaces() =
        parse ":-rule(X):-X = 1." |> check (RuleParseResult(RULE(SIGNATURE "rule" [var "X"]) (EqExpr(var "X", num 1.))))

    [<Test>]
    let parseEqGrLeRuleWithOnlyFirstSpaces() =
        parse ":-rule(X) :- X=1." |> check (RuleParseResult(RULE(SIGNATURE "rule" [var "X"]) (EqExpr(var "X", num 1.))))

    [<Test>]
    let parseMultipleRule() =
        parse ":-rule(X, R) :- R is X * 2." |> check (RuleParseResult(RULE(SIGNATURE "rule" [var "X"; var "R"]) (CalcExpr(var "R", Multiply(Value(var "X"), Value(num 2.))))))

    [<Test>]
    let parseAndRule() =
         parse ":-rule(X, Y) :- X = 1, Y = 2." |> check (RuleParseResult(RULE (SIGNATURE "rule" [var "X"; var "Y"]) (AndExpression(EqExpr(var "X", num 1.), EqExpr(var "Y", num 2.)))))
    
    [<Test>]
    let parseOrRule() =
         parse ":-rule(X, Y) :- X = 1 ; Y = 2." |> check (RuleParseResult(RULE (SIGNATURE "rule" [var "X"; var "Y"]) (OrExpression(EqExpr(var "X", num 1.), EqExpr(var "Y", num 2.)))))

    [<Test>]
    let parseRecursiveRule() =
         parse ":-rule(X, Y) :- rule(X, Y)." |> check (RuleParseResult(RULE (SIGNATURE "rule" [var "X"; var "Y"]) (CallExpression(GoalSignature("rule", toArgs [var "X"; var "Y"])))))

    [<Test>]
    let parseFactorialRule() =
         parse ":-factorial(1,1)." |> check (RuleParseResult(RULE(SIGNATURE "factorial" [num 1.; num 1.]) True))

         parse ":-factorial(X,Y) :- X > 1, X1 is X - 1, factorial(X1, Y1), Y is X * Y1." |> check (RuleParseResult(RULE (SIGNATURE "factorial" [var "X"; var "Y"]) (AndExpression(GrExpr(var "X", num 1.), AndExpression(CalcExpr(var "X1", Subsctruct(Value(var "X"), Value(num 1.))), AndExpression(GOAL "factorial" [var "X1"; var "Y1"], CalcExpr(var "Y", Multiply(Value(var "X"), Value(var "Y1")))))))))
