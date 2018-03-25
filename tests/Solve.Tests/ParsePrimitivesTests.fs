﻿module Solve.PrimitivesTests

open Solve.Tests

open NUnit.Framework
open System.Diagnostics

open Solve
open Solve.TermTypes

open TermTypes.Transformers

open Rule
open Rule.Transformers

open Solve.Parse

open FParsec

let inline parse str = Solve.Parse.Parse.parsePlString str

let inline checkSuccess x =
    function
    | Success(r, _, _) -> Assert.AreEqual(x, r)
    | Failure(_, _, _) -> Assert.Fail(sprintf "Failure instead of success in expected %A" x)

let inline checkFailure x = match x with | Failure(_,_,_) -> () | _ -> Assert.Fail("Expected fail")

[<TestFixture>]
module PrimitivesTests =
    open Solve.Parse.Primitives

    [<Test; MemoryReport>]
    let parseNumTerm() = Solve.Parse.Parse.testRun pterm "23" |> checkSuccess (num 23.)
    
    [<Test; MemoryReport>]
    let parseNumTermWithDot() = Solve.Parse.Parse.testRun (pterm .>> pstring ".") "23." |> checkSuccess (num 23.)
    
    [<Test; MemoryReport>]
    let parseListFromSingleNumber() = Solve.Parse.Parse.testRun pterm "[1]" |> checkSuccess (ListTerm(TypedListTerm(num 1., NilTerm)))
    
    [<Test; MemoryReport>]
    let parseListFromTwoDifferentTerms() = Solve.Parse.Parse.testRun pterm "[1,a]" |> checkSuccess (ListTerm(TypedListTerm(num 1., TypedListTerm(atom "a", NilTerm))))
    
    [<Test; MemoryReport>]
    let parseListWithVariableTail() = Solve.Parse.Parse.testRun pterm "[1,2|A]" |> checkSuccess (ListTerm(TypedListTerm(num 1., TypedListTerm(num 2., VarListTerm(Variable("A"))))))
    
    [<Test; MemoryReport>]
    let parseNonEmptySignature() = Solve.Parse.Parse.testRun psignature "a(1)." |> checkSuccess (SIGNATURE "a" [num 1.])
    
    [<Test; MemoryReport>]
    let parseFactWithNonEmptySignature() = Solve.Parse.Parse.testRun pfact "a(1)." |> checkSuccess (FACT (SIGNATURE "a" [num 1.]))

    [<Test; MemoryReport>]
    let parseEqBodyExpession() = Solve.Parse.Parse.testRun pbody "a12=b32" |> checkSuccess (EqExpr(atom "a12", atom "b32"))

    [<Test; MemoryReport>]
    let parseCalcBodyExpession() = Solve.Parse.Parse.testRun pbody "V is 1+2" |> checkSuccess (CalcExpr(var "V", Plus(Value(num 1.), Value(num 2.))))
    
    [<Test; MemoryReport>]
    let parseAndExpressionWithTwoEqs() = Solve.Parse.Parse.testRun pbody "a12=b32,b32=b33" |> checkSuccess (AndExpression(EqExpr(atom "a12", atom "b32"), EqExpr(atom "b32", atom "b33")))

    [<Test; MemoryReport>]
    let parseRuleWithEqExpressionAndEmptySignature() = 
        Solve.Parse.Parse.testRun prule "a():-a1=a2."
        |> checkSuccess (RULE (SIGNATURE "a" []) (EqExpr(atom "a1", atom "a2")))

    [<Test; MemoryReport>]
    let parseRuleWithEqExpressionAndNonEmptySignature() = 
        Solve.Parse.Parse.testRun prule "a12(12):-a1=a2."
        |> checkSuccess (RULE (SIGNATURE "a12" [num 12.]) (EqExpr(atom "a1", atom "a2")))

    [<Test; MemoryReport>]
    let parseRuleWithAndExpressionAndNonEmptySiganture() = 
        Solve.Parse.Parse.testRun prule "a12(12):-a1=a2,a1=b2."
        |> checkSuccess (RULE (SIGNATURE "a12" [num 12.]) (AndExpression(EqExpr(atom "a1", atom "a2"), EqExpr(atom "a1", atom "b2"))))

    [<Test; MemoryReport>]
    let parseRuleWithMultipleAnds() = 
        Solve.Parse.Parse.testRun prule "a12(12):-a1=a1,a1=a1,a1=a1,a1=a1,a1=a1,a1=a1,a1=a1,a1=a1,a1=a1."
        |> checkSuccess (RULE (SIGNATURE "a12" [num 12.]) (AndExpression(EqExpr(atom "a1", atom "a1"), AndExpression(EqExpr(atom "a1", atom "a1"), AndExpression(EqExpr(atom "a1", atom "a1"), AndExpression(EqExpr(atom "a1", atom "a1"), AndExpression(EqExpr(atom "a1", atom "a1"), AndExpression(EqExpr(atom "a1", atom "a1"), AndExpression(EqExpr(atom "a1", atom "a1"), AndExpression(EqExpr(atom "a1", atom "a1"), EqExpr(atom "a1", atom "a1")))))))))))

    [<Test; MemoryReport>]
    let parseRuleWithOneValueCalc() = 
        Solve.Parse.Parse.testRun prule "a():- X is 1."
        |> checkSuccess (RULE (SIGNATURE "a" []) (CalcExpr(var "X", Value(num 1.))))

    [<Test; MemoryReport>]
    let parseRuleWithPlusCalc() = 
        Solve.Parse.Parse.testRun prule "a1(12):-X is 1+1."
        |> checkSuccess (RULE (SIGNATURE "a1" [num 12.]) (CalcExpr(var "X", Plus(Value(num 1.), Value(num 1.)))))

    [<Test; MemoryReport>]
    let parseRuleWithSubstructCalc() = 
        Solve.Parse.Parse.testRun prule "a():- X is 2 - 1."
        |> checkSuccess (RULE (SIGNATURE "a" []) (CalcExpr(var "X", Subsctruct(Value(num 2.), Value(num 1.)))))

    [<Test; MemoryReport>]
    let parseRuleWithMultiplyCalc() = 
        Solve.Parse.Parse.testRun prule "a():- X is 2 * 1."
        |> checkSuccess (RULE (SIGNATURE "a" []) (CalcExpr(var "X", Multiply(Value(num 2.), Value(num 1.)))))

    [<Test; MemoryReport>]
    let parseRuleWithDivisionCalc() = 
        Solve.Parse.Parse.testRun prule "a():- X is 2 / 1."
        |> checkSuccess (RULE (SIGNATURE "a" []) (CalcExpr(var "X", Division(Value(num 2.), Value(num 1.)))))
        
    [<Test; MemoryReport>]
    let parseRuleWithMultipleAddsCalc() = 
        Solve.Parse.Parse.testRun prule "a1(12):-X is 1+1+1+1."
        |> checkSuccess (RULE (SIGNATURE "a1" [num 12.]) (CalcExpr(var "X", Plus(Value(num 1.), Plus(Value(num 1.), Plus(Value(num 1.), Value(num 1.)))))))
