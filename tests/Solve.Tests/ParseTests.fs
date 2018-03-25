module Solve.InteractiveTests

open Solve.Tests

open NUnit.Framework

open Solve.TermTypes
open Solve.TermTypes.Transformers
open Solve.Rule
open Solve.Rule.Transformers
open Solve.Parse

open Solve.PrimitivesTests

[<TestFixture>]
module ParserTests =
    let checkParseFailure given =
        match given with
        | ParseError _ -> ()
        | _ -> failwithf "Expected failure but was %A" given

    [<Test; MemoryReport>]
    let parsePlAssertOfFactWithNonEmptySignature() = Solve.Parse.Parse.parsePlString ":-a(1)." |> check (RuleParseResult(FACT <| SIGNATURE "a" [num 1.]))
    
    [<Test; MemoryReport>]
    let parsePlQueryForNonEmptySignature() = Solve.Parse.Parse.parsePlString "?-a(1)." |> check (CallParseResult(GOAL "a" [num 1.]))
    
    [<Test; MemoryReport>]
    let checkNoParamsFactParse() =
        parse ":-fact()."
        |> check (RuleParseResult(FACT <| SIGNATURE "fact" []))
    
    [<Test; MemoryReport>]
    let checkNumberParamFactParse() =
        parse ":-fact(1)."
        |> check (RuleParseResult(FACT <| SIGNATURE  "fact" [num 1.]))
    
    [<Test; MemoryReport>]
    let checkAtomParamFactParse() =
        parse ":-fact(a)."
        |> check (RuleParseResult(FACT <| SIGNATURE  "fact" [atom "a"]))
    
    [<Test; MemoryReport>]
    let checkEmptyListParse() =
        parse "?-list([])."
        |> check (CallParseResult(GOAL "list" [ListTerm(NilTerm)]))
    
    [<Test; MemoryReport>]
    let checkDefinedListParse() =
        parse "?-list([1,2,3])."
        |> check (CallParseResult(GOAL "list" [ListTerm(TypedListTerm(num 1., TypedListTerm(num 2., TypedListTerm(num 3., NilTerm))))]))
    
    [<Test; MemoryReport>]
    let checkPartlyDefinedListParse() =
        parse "?-list([1|X])."
        |> check (CallParseResult(GOAL "list" [ListTerm(TypedListTerm(num 1., VarListTerm(Variable("X"))))]))

    [<Test; MemoryReport>]
    let checkFailQuery() =
        parse "?-lli(()."
        |> checkParseFailure
    
    [<Test; MemoryReport>]
    let parseFacts() =
         parse ":-fact(1)." |> check (RuleParseResult(RULE(SIGNATURE "fact" [num 1.]) True))
         parse ":-fact(2)." |> check (RuleParseResult(RULE(SIGNATURE "fact" [num 2.]) True))
         parse ":-fact(X)." |> check (RuleParseResult(RULE(SIGNATURE "fact" [var "X"]) True))
         parse ":-fact(Y)." |> check (RuleParseResult(RULE(SIGNATURE "fact" [var "Y"]) True))
         parse ":-fact(x)." |> check (RuleParseResult(RULE(SIGNATURE "fact" [atom "x"]) True))
         parse ":-fact(y)." |> check (RuleParseResult(RULE(SIGNATURE "fact" [atom "y"]) True))

    [<Test; MemoryReport>]
    let parseFactWithoutDot() =
        parse ":- fact(y)" |> checkParseFailure

    [<Test; MemoryReport>]
    let parseFactWithInitialSpace() =
        parse ":- fact(y)." |> check (RuleParseResult(RULE(SIGNATURE "fact" [atom "y"]) True))

    [<Test; MemoryReport>]
    let parseFactWithTrailingSpace() =
        parse ":- fact(y). " |> check (RuleParseResult(RULE(SIGNATURE "fact" [atom "y"]) True))

    [<Test; MemoryReport>]
    let parseFactWithSpaceBeforeDot() =
        parse ":- fact(y) . " |> check (RuleParseResult(RULE(SIGNATURE "fact" [atom "y"]) True))

    [<Test; MemoryReport>]
    let parseEqGrLeRuleWithoutSpaces() =
        parse ":-rule(X):-X=1." |> check (RuleParseResult(RULE(SIGNATURE "rule" [var "X"]) (EqExpr(var "X", num 1.))))
        parse ":-rule(X):-X>1." |> check (RuleParseResult(RULE(SIGNATURE "rule" [var "X"]) (GrExpr(var "X", num 1.))))
        parse ":-rule(X):-X<1." |> check (RuleParseResult(RULE(SIGNATURE "rule" [var "X"]) (LeExpr(var "X", num 1.))))

    [<Test; MemoryReport>]
    let parseEqGrLeRuleWithSpaces() =
        parse ":-rule(X) :- X = 1." |> check (RuleParseResult(RULE(SIGNATURE "rule" [var "X"]) (EqExpr(var "X", num 1.))))
        parse ":-rule(X) :- X > 1." |> check (RuleParseResult(RULE(SIGNATURE "rule" [var "X"]) (GrExpr(var "X", num 1.))))
        parse ":-rule(X) :- X < 1." |> check (RuleParseResult(RULE(SIGNATURE "rule" [var "X"]) (LeExpr(var "X", num 1.))))

    [<Test; MemoryReport>]
    let parseEqGrLeRuleWithOnlyExprSpaces() =
        parse ":-rule(X):-X = 1." |> check (RuleParseResult(RULE(SIGNATURE "rule" [var "X"]) (EqExpr(var "X", num 1.))))

    [<Test; MemoryReport>]
    let parseEqGrLeRuleWithOnlyFirstSpaces() =
        parse ":-rule(X) :- X=1." |> check (RuleParseResult(RULE(SIGNATURE "rule" [var "X"]) (EqExpr(var "X", num 1.))))

    [<Test; MemoryReport>]
    let parseMultipleRule() =
        parse ":-rule(X, R) :- R is X * 2." |> check (RuleParseResult(RULE(SIGNATURE "rule" [var "X"; var "R"]) (CalcExpr(var "R", Multiply(Value(var "X"), Value(num 2.))))))

    [<Test; MemoryReport>]
    let parseAndRule() =
         parse ":-rule(X, Y) :- X = 1, Y = 2." |> check (RuleParseResult(RULE (SIGNATURE "rule" [var "X"; var "Y"]) (AndExpression(EqExpr(var "X", num 1.), EqExpr(var "Y", num 2.)))))
    
    [<Test; MemoryReport>]
    let parseOrRule() =
         parse ":-rule(X, Y) :- X = 1 ; Y = 2." |> check (RuleParseResult(RULE (SIGNATURE "rule" [var "X"; var "Y"]) (OrExpression(EqExpr(var "X", num 1.), EqExpr(var "Y", num 2.)))))

    [<Test; MemoryReport>]
    let parseRecursiveRule() =
         parse ":-rule(X, Y) :- rule(X, Y)." |> check (RuleParseResult(RULE (SIGNATURE "rule" [var "X"; var "Y"]) (CallExpression(GoalSignature("rule", toArgs [var "X"; var "Y"])))))

    [<Test; MemoryReport>]
    let parseFactorialRule() =
         parse ":-factorial(1,1)." |> check (RuleParseResult(RULE(SIGNATURE "factorial" [num 1.; num 1.]) True))

         parse ":-factorial(X,Y) :- X > 1, X1 is X - 1, factorial(X1, Y1), Y is X * Y1." |> check (RuleParseResult(RULE (SIGNATURE "factorial" [var "X"; var "Y"]) (AndExpression(GrExpr(var "X", num 1.), AndExpression(CalcExpr(var "X1", Subsctruct(Value(var "X"), Value(num 1.))), AndExpression(GOAL "factorial" [var "X1"; var "Y1"], CalcExpr(var "Y", Multiply(Value(var "X"), Value(var "Y1")))))))))
