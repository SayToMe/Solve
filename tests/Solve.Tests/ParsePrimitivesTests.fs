module Solve.PrimitivesTests

open Solve.Tests

open NUnit.Framework
open System.Diagnostics

open Solve
open Solve.TermTypes

open TermTypes.Transformers

open Rule
open Rule.Transformers

open Solve.PrologParser
open Solve.PrologParser.Parser

open FParsec

let inline parse str = parsePlString str

let inline checkSuccess x =
    function
    | Success(r, _, _) -> Assert.AreEqual(x, r)
    | Failure(_, err, _) -> Assert.Fail(sprintf "Failure instead of success in expected %A. Message %A" x err)

let inline checkFailure x = match x with | Failure(_,_,_) -> () | _ -> Assert.Fail("Expected fail")

[<TestFixture>]
module PrimitivesTests =
    open Solve.PrologParser.Primitives

    [<Test>]
    let parseSkipWs() = testRun ws "23" |> checkSuccess ()

    [<Test>]
    let parseSkipWs2() = testRun ws "    23    " |> checkSuccess ()

    [<Test>]
    let parseNumTerm() = testRun pterm "23" |> checkSuccess (num 23.)
    
    [<Test>]
    let parseNumTermWithDot() = testRun (pterm .>> pstring ".") "23." |> checkSuccess (num 23.)
    
    [<Test>]
    let parseListFromSingleNumber() = testRun pterm "[1]" |> checkSuccess (ListTerm(TypedListTerm(num 1., NilTerm)))
    
    [<Test>]
    let parseListFromTwoDifferentTerms() = testRun pterm "[1,a]" |> checkSuccess (ListTerm(TypedListTerm(num 1., TypedListTerm(atom "a", NilTerm))))
    
    [<Test>]
    let parseListWithVariableTail() = testRun pterm "[1,2|A]" |> checkSuccess (ListTerm(TypedListTerm(num 1., TypedListTerm(num 2., VarListTerm(Variable("A"))))))
    
    [<Test>]
    let parseNonEmptySignature() = testRun psignature "a(1)." |> checkSuccess (SIGNATURE "a" [num 1.])
    
    [<Test>]
    let parseFactWithNonEmptySignature() = testRun pfact "a(1)." |> checkSuccess (FACT (SIGNATURE "a" [num 1.]))

    [<Test>]
    let parseEqBodyExpession() = testRun pbody "a12=b32" |> checkSuccess (EqExpr(atom "a12", atom "b32"))

    [<Test>]
    let parseCalcBodyExpession() = testRun pbody "V is 1+2" |> checkSuccess (CalcExpr(var "V", Plus(Value(num 1.), Value(num 2.))))
    
    [<Test>]
    let parseAndExpressionWithTwoEqs() = testRun pbody "a12=b32,b32=b33" |> checkSuccess (AndExpression(EqExpr(atom "a12", atom "b32"), EqExpr(atom "b32", atom "b33")))

    [<Test>]
    let parseRuleWithEqExpressionAndEmptySignature() = 
        testRun prule "a():-a1=a2."
        |> checkSuccess (RULE (SIGNATURE "a" []) (EqExpr(atom "a1", atom "a2")))

    [<Test>]
    let parseRuleWithEqExpressionAndNonEmptySignature() = 
        testRun prule "a():- a1 = a2."
        |> checkSuccess (RULE (SIGNATURE "a" []) (EqExpr(atom "a1", atom "a2")))

    [<Test>]
    let parseRuleWithAndExpressionAndNonEmptySiganture() = 
        testRun prule "a():-a1=a2, b1=b2."
        |> checkSuccess (RULE (SIGNATURE "a" []) (AndExpression(EqExpr(atom "a1", atom "a2"), EqExpr(atom "b1", atom "b2"))))

    [<Test>]
    let parseRuleWithMultipleAnds() = 
        testRun prule "a12(12):-a1=a1,a1=a1,a1=a1,a1=a1,a1=a1,a1=a1,a1=a1,a1=a1,a1=a1."
        |> checkSuccess (RULE (SIGNATURE "a12" [num 12.]) (AndExpression(EqExpr(atom "a1", atom "a1"), AndExpression(EqExpr(atom "a1", atom "a1"), AndExpression(EqExpr(atom "a1", atom "a1"), AndExpression(EqExpr(atom "a1", atom "a1"), AndExpression(EqExpr(atom "a1", atom "a1"), AndExpression(EqExpr(atom "a1", atom "a1"), AndExpression(EqExpr(atom "a1", atom "a1"), AndExpression(EqExpr(atom "a1", atom "a1"), EqExpr(atom "a1", atom "a1")))))))))))

    [<Test>]
    let parseRuleWithOneValueCalc() = 
        testRun prule "a():- X is 1."
        |> checkSuccess (RULE (SIGNATURE "a" []) (CalcExpr(var "X", Value(num 1.))))

    [<Test>]
    let parseRuleWithPlusCalc() = 
        testRun prule "a1(12):-X is 1+1."
        |> checkSuccess (RULE (SIGNATURE "a1" [num 12.]) (CalcExpr(var "X", Plus(Value(num 1.), Value(num 1.)))))

    [<Test>]
    let parseRuleWithSubstructCalc() = 
        testRun prule "a():- X is 2 - 1."
        |> checkSuccess (RULE (SIGNATURE "a" []) (CalcExpr(var "X", Subsctruct(Value(num 2.), Value(num 1.)))))

    [<Test>]
    let parseRuleWithMultiplyCalc() = 
        testRun prule "a():- X is 2 * 1."
        |> checkSuccess (RULE (SIGNATURE "a" []) (CalcExpr(var "X", Multiply(Value(num 2.), Value(num 1.)))))

    [<Test>]
    let parseRuleWithDivisionCalc() = 
        testRun prule "a():- X is 2 / 1."
        |> checkSuccess (RULE (SIGNATURE "a" []) (CalcExpr(var "X", Division(Value(num 2.), Value(num 1.)))))
        
    [<Test>]
    let parseRuleWithMultipleAddsCalc() = 
        testRun prule "a1(12):-X is 1+1+1+1."
        |> checkSuccess (RULE (SIGNATURE "a1" [num 12.]) (CalcExpr(var "X", Plus(Value(num 1.), Plus(Value(num 1.), Plus(Value(num 1.), Value(num 1.)))))))
