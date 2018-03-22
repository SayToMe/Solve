module Solve.ParseTests

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
module PrimsTests =
    [<Test; MemoryReport>]
    let parseNumTerm() = Solve.Parse.Parse.testRun Solve.Parse.Prims.pterm "23" |> checkSuccess (num 23.)
    
    [<Test; MemoryReport>]
    let parseListFromSingleNumber() = Solve.Parse.Parse.testRun Solve.Parse.Prims.pterm "[1]" |> checkSuccess (ListTerm(TypedListTerm(num 1., NilTerm)))
    
    [<Test; MemoryReport>]
    let parseListFromTwoDifferentTerms() = Solve.Parse.Parse.testRun Solve.Parse.Prims.pterm "[1,a]" |> checkSuccess (ListTerm(TypedListTerm(num 1., TypedListTerm(atom "a", NilTerm))))
    
    [<Test; MemoryReport>]
    let parseListWithVariableTail() = Solve.Parse.Parse.testRun Solve.Parse.Prims.pterm "[1,2|A]" |> checkSuccess (ListTerm(TypedListTerm(num 1., TypedListTerm(num 2., VarListTerm(Variable("A"))))))
    
    [<Test; MemoryReport>]
    let parseNonEmptySignature() = Solve.Parse.Parse.testRun Solve.Parse.Prims.psignature "a(1)." |> checkSuccess (SIGNATURE "a" [num 1.])
    
    [<Test; MemoryReport>]
    let parseFactWithNonEmptySignature() = Solve.Parse.Parse.testRun Solve.Parse.Prims.pfact "a(1)." |> checkSuccess (FACT (SIGNATURE "a" [num 1.]))

    [<Test; MemoryReport>]
    let parseEqBodyExpession() = Solve.Parse.Parse.testRun Solve.Parse.Prims.pbody "a12=b32" |> checkSuccess (EqExpr(atom "a12", atom "b32"))

    [<Test; MemoryReport>]
    let parseCalcBodyExpession() = Solve.Parse.Parse.testRun Solve.Parse.Prims.pbody "V is 1+2" |> checkSuccess (CalcExpr(var "V", Plus(Value(num 1.), Value(num 2.))))
    
    [<Test; MemoryReport>]
    let parseAndExpressionWithTwoEqs() = Solve.Parse.Parse.testRun Solve.Parse.Prims.pbody "a12=b32,b32=b33" |> checkSuccess (AndExpression(EqExpr(atom "a12", atom "b32"), EqExpr(atom "b32", atom "b33")))
    
    [<Test; MemoryReport>]
    let parseRuleWithEqExpressionAndNonEmptySignature() = 
        Solve.Parse.Parse.testRun Solve.Parse.Prims.prule "a12(12):-a1=a2."
        |> checkSuccess (RULE (SIGNATURE "a12" [num 12.]) (EqExpr(atom "a1", atom "a2")))

    [<Test; MemoryReport>]
    let parseRuleWithAndExpressionAndNonEmptySiganture() = 
        Solve.Parse.Parse.testRun Solve.Parse.Prims.prule "a12(12):-a1=a2,a1=b2."
        |> checkSuccess (RULE (SIGNATURE "a12" [num 12.]) (AndExpression(EqExpr(atom "a1", atom "a2"), EqExpr(atom "a1", atom "b2"))))

    [<Test; MemoryReport>]
    let parseRuleWithMultipleAnds() = 
        Solve.Parse.Parse.testRun Solve.Parse.Prims.prule "a12(12):-a1=a1,a1=a1,a1=a1,a1=a1,a1=a1,a1=a1,a1=a1,a1=a1,a1=a1."
        |> checkSuccess (RULE (SIGNATURE "a12" [num 12.]) (AndExpression(EqExpr(atom "a1", atom "a1"), AndExpression(EqExpr(atom "a1", atom "a1"), AndExpression(EqExpr(atom "a1", atom "a1"), AndExpression(EqExpr(atom "a1", atom "a1"), AndExpression(EqExpr(atom "a1", atom "a1"), AndExpression(EqExpr(atom "a1", atom "a1"), AndExpression(EqExpr(atom "a1", atom "a1"), AndExpression(EqExpr(atom "a1", atom "a1"), EqExpr(atom "a1", atom "a1")))))))))))

[<TestFixture>]
module ParserTests =
    let checkParseFailure given =
        match given with
        | ParseError _ -> ()
        | _ -> failwithf "Expected failure but was %A" expected

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