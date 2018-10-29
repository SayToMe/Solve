namespace Solve.Tests
open System
open NUnit.Framework

open NUnit.Framework
open System.Diagnostics

open Solve

open TermTypes
open TermTypes.Transformers

open Solve.Tests.Common

[<TestFixture>]
module ChangeVariablesChangeVariableTests =
    let getChangeVariableFunction var n =
        function
        | Variable(v) when v = var -> num n
        | v -> VariableTerm(v)

    [<Test>]
    let ``Given test(N1, N, N) with N -> 1 should return test(N1, 1, 1)``() =
        let changeVariable = getChangeVariableFunction "N" 1.
        VariableUnify.changeVariablesRecursive changeVariable (anyStruct "test" [var "N1"; var "N"; var "N"])
        |> check (anyStruct "test" [var "N1"; num 1.; num 1.])
