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
module VariableUnifyTests =
    let getChangeVariableFunction var n =
        function
        | Variable(v) when v = var -> num n
        | v -> VariableTerm(v)

    [<Test>]
    let ``process struct test``() =
        let changeVariable = getChangeVariableFunction "N" 1.
        VariableUnify.changeVariablesForStruct changeVariable (Structure("test", [var "N1"; var "N"; var "N"]))
        |> check (Structure("test", [var "N1"; num 1.; num 1.]))
        
    [<Test>]
    let ``post unify params with arguments test3``() =
        VariableUnify.unifyParametersWithArguments (toParams [num 10.; num 5.; var "V"]) (toArgs [num 10.; num 5.; var "V"])
        |> check (Some([num 10.; num 5.; var "V"]))
        VariableUnify.unifyParametersWithArguments (toParams [num 10.; num 5.; var "V"]) (toArgs [var "V"; var "V"; var "V"])
        |> check (Some([num 10.; num 5.; var "V"]))
        VariableUnify.unifyParametersWithArguments (toParams [var "V"; var "V"; var "V"]) (toArgs [num 10.; num 5.; var "V"])
        |> check (Some([num 10.; num 5.; var "V"]))

        VariableUnify.unifyParametersWithArguments (toParams [var "N"]) (toArgs [var "N2"]) |> check (Some([var "N"]))
        VariableUnify.unifyParametersWithArguments (toParams [num 1.]) (toArgs [var "N"]) |> check (Some([num 1.]))
        VariableUnify.unifyParametersWithArguments (toParams [var "N"]) (toArgs [num 1.]) |> check (Some([num 1.]))
        VariableUnify.unifyParametersWithArguments (toParams [num 1.]) (toArgs [num 1.]) |> check (Some([num 1.]))
        VariableUnify.unifyParametersWithArguments (toParams [num 1.]) (toArgs [num 2.]) |> check None
