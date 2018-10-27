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

open Solve

[<TestFixture>]
module SolveTests =
    [<Test>]
    let ``Given `eq1(N):- N = 1.` solve with eq1(N) should return [N = 1]``() = 
        solve (GOAL "eq1" [var "N"]) [RULE (SIGNATURE "eq1" [var "N"]) (EqExpr(var "N", num 1.))]
        |> checkSolve [[Variable "N", num 1.]]

    [<Test>]
    let ``Given `eq2(N):- N = 1.` solve with eq2(1) should return true``() = 
        solve (GOAL "eq2" [num 1.]) [RULE (SIGNATURE "eq2" [var "N"]) (EqExpr(var "N", num 1.))]
        |> checkSolve [[]]

    [<Test>]
    let ``Given `eq3(N):- N = 1.` solve with eq3(2) should return false``() = 
        solve (GOAL "eq3" [num 2.]) [RULE (SIGNATURE "eq3" [var "N"]) (EqExpr(var "N", num 1.))]
        |> checkSolve []

    [<Test>]
    let ``Given `and(N):- N = 1, N = 2.` solve with and(N) should return false``() = 
        solve (GOAL "and" [var "N"]) [RULE (SIGNATURE "and" [var "N"]) (AndExpression(EqExpr(var "N", num 1.), EqExpr(var "N", num 2.)))]
        |> checkSolve []
        
    [<Test>]
    let ``Given `or(N):- N = 1; N = 2.` solve with or(N) should return [N = 1], [N = 2]``() = 
        solve (GOAL "or" [var "N"]) [RULE (SIGNATURE "or" [var "N"]) (OrExpression(EqExpr(var "N", num 1.), EqExpr(var "N", num 2.)))]
        |> checkSolve [[Variable "N", num 1.]; [Variable "N", num 2.]]

    [<Test>]
    let ``Given `fa(N):- False.` solve with fa(N) should return false``() = 
        solve (GOAL "fa" [var "N"]) [RULE (SIGNATURE "fa" [var "N"]) (False)]
        |> checkSolve []

    [<Test>]
    let ``Given `innervar(N):- Temp = 1, N = 1.` solve with innervar(N) should return [N = 1]``() = 
        solve (GOAL "innervar" [var "N"]) [RULE (SIGNATURE "innervar" [var "N"]) (AndExpression(EqExpr(var "Temp", num 1.), EqExpr(var "N", var "Temp")))]
        |> checkSolve [[Variable "N", num 1.]]

    [<Test>]
    let ``Given `structureRule(N, R):- R is N + 1.` with structureRule(2, Res) should return [Res = 3]``() =
        solve (GOAL "structureRule" [num 2.; var "Res"]) [RULE (SIGNATURE "structureRule" [var "N"; var "R"]) (CalcExpr(var "R", Value(StructureTerm(Structure("+", [var "N"; num 1.])))))]
        |> checkSolve [[Variable "Res", num 3.]]

    [<Test>]
    let ``Given `cut(R):- (R = 1; R = 2), !.` solve with cut(R) should return [R = 1]``() =
        solve (GOAL "cut" [var "R"]) [RULE (SIGNATURE "cut" [var "R"]) (AndExpression(OrExpression(EqExpr(var "R", num 1.), EqExpr(var "R", num 2.)), Cut))]
        |> checkSolve [[Variable "R", num 1.]]

    [<Test>]
    let ``Given `cut(R1, R2):- (R1 = 1; R1 = 2), (R2 = 1; R2 = 2), !.` solve with cut(R1, R2) should return [R1 = 1, R2 = 1]``() =
        solve (GOAL "cut" [var "R1"; var "R2"]) [RULE (SIGNATURE "cut" [var "R1"; var "R2"]) (AndExpression(AndExpression(OrExpression(EqExpr(var "R1", num 1.), EqExpr(var "R1", num 2.)), OrExpression(EqExpr(var "R2", num 1.), EqExpr(var "R2", num 2.))), Cut))]
        |> checkSolve [[Variable "R1", num 1.; Variable "R2", num 1.]]

    [<Test>]
    let ``Given `lazy_infinite(C, R):- (C = R); (NextC is C + 1, lazy_infinite(NextC, R)).` solve with lazy_infinite(1, R) top 3 should return [R = 1], [R = 2], [R = 3]``() =
        solve (GOAL "lazy_infinite" [num 1.; var "R"]) [RULE (SIGNATURE "lazy_infinite" [var "C"; var "R"]) (OrExpression(EqExpr(var "C", var "R"), AndExpression(CalcExpr(var "NextC", Plus(Value(var "C"), Value(num 1.))), GOAL "lazy infinite" [var "NextC"; var "R"])))]
        |> Seq.take 3
        |> checkSolve ([1..3] |> List.map (fun x -> [Variable "R", num (float x)]))
        
    [<Test>]
    let ``Given `eq1_both(N1, N2):- N1 = 1, N2 = 1.` solve with eq1_both(N, Res) should return [N = 1; Res = 1]``() =
        solve (GOAL "eq1_both" [var "N"; var "Res"]) [RULE (SIGNATURE "eq1_both" [var "N1"; var "N2"]) (AndExpression((EqExpr(var "N1", num 1.), (EqExpr(var "N2", num 1.)))))]
        |> checkSolve [[Variable "N", num 1.; Variable "Res", num 1.]]
        
    [<Test>]
    let ``Given `eq(N1, N2):- N1 = N2.` solve with eq(N, N2) should return [N = N2]``() =
        solve(GOAL "eq" [var "N"; var "N2"]) [RULE (SIGNATURE "eq" [var "N1"; var "N2"]) (EqExpr(var "N1", var "N2"))]
        |> checkSolve [[Variable "N", var "N2"]]

    [<Test>]
    let ``Given `f1(N, Res):- (N = 1, Res = 1); (N > 1, Res = 2)` solve with f1(1, Res) should return [Res = 1]``() =
        let oneOrTwoRule = RULE(SIGNATURE "f1" [var "N"; var "Res"]) (OrExpression(AndExpression(EqExpr(var "N", num 1.), EqExpr(var "Res", num 1.)), AndExpression(GrExpr(var "N", num 1.), EqExpr(var "Res", num 2.))))
        solve (GOAL "f1" [num 1.; var "Res"]) [oneOrTwoRule]
        |> checkSolve [[Variable "Res", num 1.]]

    [<Test>]
    let ``Given `f1(N, Res):- (N = 1, Res = 1); (N > 1, Res = 2)` solve with f1(3, Res) should return [Res = 2]``() =
        let oneOrTwoRule = RULE(SIGNATURE "f1" [var "N"; var "Res"]) (OrExpression(AndExpression(EqExpr(var "N", num 1.), EqExpr(var "Res", num 1.)), AndExpression(GrExpr(var "N", num 1.), EqExpr(var "Res", num 2.))))
        solve (GOAL "f1" [num 3.; var "Res"]) [oneOrTwoRule]
        |> checkSolve [[Variable "Res", num 2.]]

    [<Test>]
    let ``Given `getn(R):- R = 1. inn(Res):- getn(Res).` solve with inn(R) should return [R = 1]``() =
        let getN = RULE(SIGNATURE "getn" [var "R"]) (EqExpr(var "R", num 1.))
        let inn = RULE(SIGNATURE "inn" [var "Res"]) (CallExpression(GoalSignature("getn", toArgs [var "Res"])))
        solve (GOAL "inn" [var "R"]) [getN; inn]
        |> checkSolve [[Variable "R", num 1.]]
        
    [<Test>]
    let ``Given `F0(1). F1(X):- F0(X), F0(X). F2(X1):- F1(X1), F1(X1), F1(X1).` solve with F2(N) should return [N = 1]``() =
        let r0 = RULE (SIGNATURE "F0" [num 1.]) True
        let r1 = RULE (SIGNATURE "F1" [var "X"]) (AndExpression(GOAL "F0" [var "X"], GOAL "F0" [var "X"]))
        let r2 = RULE (SIGNATURE "F2" [var "X1"]) (AndExpression(GOAL "F1" [var "X1"], AndExpression(GOAL "F1" [var "X1"], GOAL "F1" [var "X1"])))
        solve (GOAL "F2" [var "N"]) [r0; r1; r2]
        |> checkSolve [[Variable "N", num 1.]]

    [<Test>]
    let ``Given factorial rule solve with 1..10 should return first 10 factorial numbers``() =
        let leftOr = AndExpression(EqExpr(var "N", num 1.), EqExpr(var "Res", num 1.))
        let rightOr = AndExpression(GrExpr(var "N", num 1.), AndExpression(CalcExpr(var "N1", Subsctruct(Value(var "N"), Value(num 1.))), AndExpression(GOAL "factorial" [var "N1"; var "R1"], CalcExpr(var "Res", Multiply(Value(var "R1"), Value(var "N"))))))
        let factorial = RULE(SIGNATURE "factorial" [var "N"; var "Res"]) (OrExpression(leftOr, rightOr))

        let knowledgebase = [
            factorial
        ]
        
        let checkf n =
            let rec f x = if x = 1. then 1. else x * f(x - 1.)
            
            solve (GOAL "factorial" [num n; var "Res"]) knowledgebase
            |> checkSolve [[Variable "Res",  num (f n)]]

        [1..10] |> List.iter (float >> checkf)
        
    [<Test>]
    let ``Given factorial rule with cut solve with 1..10 should return first 10 factorial numbers``() =
        let leftOr = AndExpression(AndExpression(EqExpr(var "N", num 1.), EqExpr(var "Res", num 1.)), Cut)
        let rightOr = AndExpression(CalcExpr(var "N1", Subsctruct(Value(var "N"), Value(num 1.))), AndExpression(GOAL "factorial" [var "N1"; var "R1"], CalcExpr(var "Res", Multiply(Value(var "R1"), Value(var "N")))))
        let factorial = RULE(SIGNATURE "factorial" [var "N"; var "Res"]) (OrExpression(leftOr, rightOr))

        let knowledgebase = [
            factorial
        ]
        
        let checkf n =
            let rec f x = if x = 1. then 1. else x * f(x - 1.)
            
            solve (GOAL "factorial" [num n; var "Res"]) knowledgebase
            |> checkSolve [[Variable "Res", num (f n)]]

        [1..10] |> List.iter (float >> checkf)

    [<Test>]
    let ``Given `equals(X, X):- True.` solve with equals(X, 1) should return X = 1.``() =
        let head = RULE (SIGNATURE "equals" [var "X"; var "X"]) True
        solve (GOAL "equals" [var "X"; num 1.]) [head]
        |> checkSolve [[Variable "X", num 1.]]

    [<Test>]
    let ``Given `head(X, [X | Y]:- True.` solve with head(1, [1, 2, 3]) should return true``() =
        let head = RULE (SIGNATURE "head" [var "X"; ListTerm(TypedListTerm(var "X", VarListTerm(Variable "Y")))]) True
        solve (GOAL "head" [num 1.; numList [1.; 2.; 3.]]) [head]
        |> checkSolve [[]]

    [<Test>]
    let ``Given `head(X, [X | Y]:- True.` solve with head(X, [1, 2, 3]) should return [X = 1]``() =
        let head = RULE (SIGNATURE "head" [var "X"; ListTerm(TypedListTerm(var "X", VarListTerm(Variable "Y")))]) True
        solve (GOAL "head" [var "X"; numList [1.; 2.; 3.]]) [head]
        |> checkSolve [[Variable "X", num 1.]]
