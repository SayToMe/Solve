module Solve.ParseTests

open Solve.Tests

open NUnit.Framework
open System.Diagnostics

open Solve
open Solve.TermTypes

open TermTypes.Transformers

open Rule
open Rule.Transformers

let parse = Solve.Parse.parsePlString

[<TestFixture>]
module ParserTests =
    [<Test; MemoryReport>]
    let checkEmptyListParse() =
        parse "?- list([])."
        |> check (CallParseResult(GOAL "list" [ListTerm(NilTerm)]))
        
    [<Test; MemoryReport>]
    let checkDefinedListParse() =
        parse "?- list([1,2,3])."
        |> check (CallParseResult(GOAL "list" [ListTerm(TypedListTerm(num 1., TypedListTerm(num 2., TypedListTerm(num 3., NilTerm))))]))

    [<Test; MemoryReport>]
    let checkPartlyDefinedListParse() =
        parse "?- list([1 | X])."
        |> check (CallParseResult(GOAL "list" [ListTerm(TypedListTerm(num 1., VarListTerm(Variable("X"))))]))
