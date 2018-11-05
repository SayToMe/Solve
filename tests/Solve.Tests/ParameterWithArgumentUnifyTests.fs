namespace Solve.Tests
open NUnit.Framework

open Solve

open TermTypes
open TermTypes.Transformers

open Rule
open Rule.Transformers

open Solve.Tests.Common

[<TestFixture>]
module ParametersWithArgumentsUnifyTests =
    [<Test>]
    let ``Given (10, 5, V) with (10, 5, V) should return (10, 5, V)``() =
        VariableUnify.unifyParametersWithArguments (toParams [num 10.; num 5.; var "V"]) (toArgs [num 10.; num 5.; var "V"])
        |> check (Some([num 10.; num 5.; var "V"]))
    
    [<Test>]
    let ``Given (10, 5, V) with (V, V, V) should return None``() =
        VariableUnify.unifyParametersWithArguments (toParams [num 10.; num 5.; var "V"]) (toArgs [var "V"; var "V"; var "V"])
        |> check None
        
    [<Test>]
    let ``Given (V, V, V) with (10, 5, V) should return None``() =
        VariableUnify.unifyParametersWithArguments (toParams [var "V"; var "V"; var "V"]) (toArgs [num 10.; num 5.; var "V"])
        |> check None

    [<Test>]
    let ``Given (V, V) with (10, 5) should return None``() =
        VariableUnify.unifyParametersWithArguments (toParams [var "V"; var "V"]) (toArgs [num 10.; num 5.])
        |> check None

    [<Test>]
    let ``Given (10, 5) with (V, V) should return None``() =
        VariableUnify.unifyParametersWithArguments (toParams [num 10.; num 5.]) (toArgs [var "V"; var "V"])
        |> check None

    [<Test>]
    let ``Given (N) with (N2) should return (N)``() =
        VariableUnify.unifyParametersWithArguments (toParams [var "N"]) (toArgs [var "N2"])
        |> check (Some([var "N"]))
            
    [<Test>]
    let ``Given (1) with (N) should return (1)``() =
        VariableUnify.unifyParametersWithArguments (toParams [num 1.]) (toArgs [var "N"])
        |> check (Some([num 1.]))
        
    [<Test>]
    let ``Given (N) with (1) should return (1)``() =
        VariableUnify.unifyParametersWithArguments (toParams [var "N"]) (toArgs [num 1.])
        |> check (Some([num 1.]))
        
    [<Test>]
    let ``Given (1) with (1) should return (1)``() =
        VariableUnify.unifyParametersWithArguments (toParams [num 1.]) (toArgs [num 1.])
        |> check (Some([num 1.]))

    [<Test>]
    let ``Given (1) with (2) should return None``() =
        VariableUnify.unifyParametersWithArguments (toParams [num 1.]) (toArgs [num 2.])
        |> check None

    [<Test>]
    let ``Given ([[] | Y]) unify with ([[] | Y]) should return ([[] | Y])``() = 
        VariableUnify.unifyParametersWithArguments [Parameter(ListTerm(TypedListTerm(VariableTerm(Variable("Y")), NilTerm)))] [Argument(ListTerm(TypedListTerm(VariableTerm(Variable("Y")), NilTerm)))]
        |> check (Some([ListTerm(TypedListTerm(VariableTerm(Variable("Y")), NilTerm))]))
