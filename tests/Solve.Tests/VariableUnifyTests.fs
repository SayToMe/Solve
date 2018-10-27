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

    module UnifyTerms =
        let unifyTerms source dest = VariableUnify.unifyTerms (VariableUnify.Source source) (VariableUnify.Dest dest)
        let checkUnifyTerms expected actual = Assert.AreEqual(expected |> Option.map VariableUnify.Unified, actual)
    
        [<Test>]
        let ``Given 1 unify with 1 should return 1``() =
            unifyTerms (num 1.) (num 1.)
            |> checkUnifyTerms (Some <| num 1.)
    
        [<Test>]
        let ``Given 1 unify with 2 should return None``() =
            unifyTerms (num 1.) (num 2.)
            |> checkUnifyTerms (None)
    
        [<Test>]
        let ``Given X unify with 1 should return 1``() =
            unifyTerms (var "X") (num 1.)
            |> checkUnifyTerms (Some (num 1.))
    
        [<Test>]
        let ``Given 1 unify with X should return 1``() =
            unifyTerms (num 1.) (var "X")
            |> checkUnifyTerms (Some (num 1.))
    
        [<Test>]
        let ``Given X unify with Y should return Y``() =
            unifyTerms (var "X") (var "Y")
            |> checkUnifyTerms (Some (var "Y"))
    
        [<Test>]
        let ``Given [] unify with [] should return []``() =
            unifyTerms (numList []) (numList [])
            |> checkUnifyTerms (Some (numList []))
    
        [<Test>]
        let ``Given [1] unify with [1] should return [1]``() =
            unifyTerms (numList [1.]) (numList [1.])
            |> checkUnifyTerms (Some (numList [1.]))
    
        [<Test>]
        let ``Given [1] unify with [2] should return None``() =
            unifyTerms (numList [1.]) (numList [2.])
            |> checkUnifyTerms (None)
    
        [<Test>]
        let ``Given [1; 2] unify with [X; X] should return None``() =
            unifyTerms (anyList [num 1.; num 2.]) (anyList [var "X"; var "X"])
            |> checkUnifyTerms (None)
    
        [<Test>]
        let ``Given [1, X, 3] unify with [A, 2, C] should return [1, 2, 3]``() =
            unifyTerms (anyList [num 1.; var "X"; num 3.]) (anyList [var "A"; num 2.; var "C"])
            |> checkUnifyTerms (Some (numList [1.; 2.; 3.]))
    
        [<Test>]
        let ``Given [1, X, 3] unify with [X, 2, Y] should return [1, 2, 3]``() =
            unifyTerms (anyList [num 1.; var "X"; num 3.]) (anyList [var "X"; num 2.; var "Y"])
            |> checkUnifyTerms (Some (numList [1.; 2.; 3.]))
    
        [<Test>]
        let ``Given [1, X, 3] unify with [1, X, Y] should return [1, X, 3]``() =
            unifyTerms (anyList [num 1.; var "X"; num 3.]) (anyList [num 1.; var "X"; var "Y"])
            |> checkUnifyTerms (Some (anyList [num 1.; var "X"; num 3.]))
    
        [<Test>]
        let ``Given [X; X; X] unify with [A; B; C] should return [A; A; A]``() =
            unifyTerms (anyList [var "X"; var "X"; var "X"]) (anyList [var "A"; var "B"; var "C"])
            |> checkUnifyTerms (Some (anyList [var "A"; var "A"; var "A"]))
    
        [<Test>]
        let ``Given  [A; B; C] unify with [X; X; X] should return [X; X; X]``() =
            unifyTerms (anyList [var "A"; var "B"; var "C"]) (anyList [var "X"; var "X"; var "X"])
            |> checkUnifyTerms (Some (anyList [var "X"; var "X"; var "X"]))
    
        [<Test>]
        let ``Given  [1; B; C] unify with [X; X; X] should return [1; 1; 1]``() =
            unifyTerms (anyList [num 1.; var "B"; var "C"]) (anyList [var "X"; var "X"; var "X"])
            |> checkUnifyTerms (Some (anyList [num 1.; num 1.; num 1.]))
    
        [<Test>]
        let ``Given  [X; X] unify with [1; X] should return [1; 1]``() =
            unifyTerms (anyList [var "X"; var "X"]) (anyList [num 1.; var "X"])
            |> checkUnifyTerms (Some (anyList [num 1.; num 1.]))

        [<Test>]
        let ``Given  [X; X] unify with [X; 1] should return [1; 1]``() =
            unifyTerms (anyList [var "X"; var "X"]) (anyList [var "X"; num 1.])
            |> checkUnifyTerms (Some (anyList [num 1.; num 1.]))

        [<Test>]
        let ``Given [] unify with [1 | X] should return None``() =
            unifyTerms (anyList []) (anyListVar [num 1.] "X")
            |> checkUnifyTerms (None)
    
        [<Test>]
        let ``Given [1] unify with [1 | X] should return [1]``() =
            unifyTerms (anyList [num 1.]) (anyListVar [num 1.] "X")
            |> checkUnifyTerms (Some (anyList [num 1.]))
    
        [<Test>]
        let ``Given [1, 2, 3] unify with [1 | X] should return [1, 2, 3]``() =
            unifyTerms (anyList [num 1.; num 2.; num 3.]) (anyListVar [num 1.] "X")
            |> checkUnifyTerms (Some (anyList [num 1.; num 2.; num 3.]))
    
        [<Test>]
        let ``Given [X] unify with [X | Y] should return [X]``() =
            unifyTerms (anyList [num 1.; var "X"; num 3.]) (anyList [num 1.; var "X"; var "Y"])
            |> checkUnifyTerms (Some (anyList [num 1.; var "X"; num 3.]))

        [<Test>]
        let ``Given a() unify with b() should return None``() =
            unifyTerms (anyStruct "a" []) (anyStruct "b" [])
            |> checkUnifyTerms (None)

        [<Test>]
        let ``Given a() unify with a() should return a()``() =
            unifyTerms (anyStruct "a" []) (anyStruct "a" [])
            |> checkUnifyTerms (Some <| anyStruct "a" [])

        [<Test>]
        let ``Given a(1) unify with a(1) should return a(1)``() =
            unifyTerms (anyStruct "a" [num 1.]) (anyStruct "a" [num 1.])
            |> checkUnifyTerms (Some <| anyStruct "a" [num 1.])

        [<Test>]
        let ``Given a(1) unify with a(2) should return None``() =
            unifyTerms (anyStruct "a" [num 1.]) (anyStruct "a" [num 2.])
            |> checkUnifyTerms (None)

        [<Test>]
        let ``Given a(X) unify with a(Y) should return a(Y)``() =
            unifyTerms (anyStruct "a" [var "X"]) (anyStruct "a" [var "Y"])
            |> checkUnifyTerms (Some <| anyStruct "a" [var "Y"])

        [<Test>]
        let ``Given a(1, X, 3, D) unify with a(X, 2, Y, Z) should return a(1, 2, 3, Z)``() =
            unifyTerms (anyStruct "a" [num 1.; var "X"; num 3.; var "D"]) (anyStruct "a" [var "X"; num 2.; var "Y"; var "Z"])
            |> checkUnifyTerms (Some <| anyStruct "a" [num 1.; num 2.; num 3.; var "Z"])

    module ChangeVariables =
        [<Test>]
        let ``Given test(N1, N, N) with N -> 1 should return test(N1, 1, 1)``() =
            let changeVariable = getChangeVariableFunction "N" 1.
            VariableUnify.changeVariablesRecursive changeVariable (anyStruct "test" [var "N1"; var "N"; var "N"])
            |> check (anyStruct "test" [var "N1"; num 1.; num 1.])
            
    module UnifyParametersWithArguments =
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
