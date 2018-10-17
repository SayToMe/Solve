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
module OntologyTests =
    let person p = RULE(SIGNATURE "person" [stringList p]) True
    let parent p d = RULE(SIGNATURE "parent" [stringList p; stringList d]) True
    let notParent = RULE(SIGNATURE "notParent" [var "P"]) (AndExpression(GOAL "person" [var "P"], NotExpression(AndExpression(GOAL "person" [var "C"], GOAL "parent" [var "P"; var "C"]))))
    let grandparent = RULE(SIGNATURE "grandparent" [var "G"; var "D"]) (AndExpression(GOAL "parent" [var "G"; var "P"], GOAL "parent" [var "P"; var "D"]))

    let knowledgebase = [
        person "Mary";
        person "Polina";
        person "Evgeniy";
        person "Solniwko";

        parent "Mary" "Polina";
        parent "Solniwko" "Polina";
        parent "Polina" "Evgeniy";

        grandparent
        notParent
    ]
    
    [<Test>]
    let ``test defined exist person rule``() =
        solve (GOAL "person" [stringList "Polina"]) knowledgebase
        |> checkSolve [[]]
        
    [<Test>]
    let ``test defined absent person rule``() =
        solve (GOAL "person" [stringList "Miwa"]) knowledgebase
        |> checkSolve []

    [<Test>]
    let ``test all persons rule``() =
        solve (GOAL "person" [var "X"]) knowledgebase
        |> checkSolve [[Variable "X", stringList "Mary"]; [Variable "X", stringList "Polina"]; [Variable "X", stringList "Evgeniy"]; [Variable "X", stringList "Solniwko"]]

    [<Test>]
    let testParentRule() =
        solve (GOAL "parent" [stringList "Polina"; var "Descendant"]) knowledgebase
        |> checkSolve [[Variable "Descendant",  stringList "Evgeniy"]]
        solve (GOAL "parent" [var "Parent"; var "Descendant"]) knowledgebase
        |> checkSolve [[Variable "Parent", stringList "Mary"; Variable "Descendant", stringList "Polina"]; [Variable "Parent", stringList "Solniwko"; Variable "Descendant", stringList "Polina"]; [Variable "Parent", stringList "Polina"; Variable "Descendant", stringList "Evgeniy"]]
        
    [<Test>]
    let testParentBidirectRule_person_first() =
        let biparent_pf = RULE(SIGNATURE "biparent_person_first" [var "P"; var "C"]) (AndExpression(GOAL "person" [var "P"], (AndExpression(GOAL "person" [var "C"], GOAL "parent" [var "P"; var "C"]))))
        let knowledgebase = knowledgebase@[biparent_pf]
        
        solve (GOAL "biparent_person_first" [var "Parent"; var "Descendant"]) knowledgebase
        |> checkSolve [[Variable "Parent", stringList "Mary"; Variable "Descendant", stringList "Polina"]; [Variable "Parent", stringList "Polina"; Variable "Descendant", stringList "Evgeniy"]; [Variable "Parent", stringList "Solniwko"; Variable "Descendant", stringList "Polina"]]
        
    [<Test>]
    let testParentBidirectRule_person_last() =
        let biparent_pl = RULE(SIGNATURE "biparent_person_last" [var "P"; var "C"]) (AndExpression(GOAL "parent" [var "P"; var "C"], AndExpression(GOAL "person" [var "P"], GOAL "person" [var "C"])))
        let knowledgebase = knowledgebase@[biparent_pl]
        
        solve (GOAL "biparent_person_last" [var "Parent"; var "Descendant"]) knowledgebase
        |> checkSolve [[Variable "Parent", stringList "Mary"; Variable "Descendant", stringList "Polina"]; [Variable "Parent", stringList "Solniwko"; Variable "Descendant", stringList "Polina"]; [Variable "Parent", stringList "Polina"; Variable "Descendant", stringList "Evgeniy"]]
        
    [<Test>]
    let testNotParentRule() =
        solve (GOAL "notParent" [var "NotParent"]) knowledgebase
        |> checkSolve [[Variable "NotParent", stringList "Evgeniy"]]

        solve (GOAL "notParent" [stringList "Mary"]) knowledgebase
        |> checkSolve []

    [<Test>]
    let testGrandparentRule() =
        solve (GOAL "grandparent" [var "GrandParent"; var "Descendant"]) knowledgebase
        |> checkSolve [[Variable "GrandParent", stringList "Mary"; Variable "Descendant", stringList "Evgeniy"]; [Variable "GrandParent", stringList "Solniwko"; Variable "Descendant", stringList "Evgeniy"]]
        solve (GOAL "grandparent" [stringList "Mary"; stringList "Evgeniy"]) knowledgebase
        |> checkSolve [[]]

    //[<Test>]
    let bigTest() =
        let r = System.Random()
        let persons = [1..1000] |> List.map (fun i -> System.Guid.NewGuid().ToString()) |> List.map person
        let gerRuleName (Rule(Signature(name, _), _)) = name
        let rec generate genFn =
            let pi = r.Next(persons.Length)
            let ci = r.Next(persons.Length)
            if pi = ci then
                generate genFn
            else
                genFn (gerRuleName persons.[pi]) (gerRuleName persons.[ci])

        let parents = [1..1000] |> List.map (fun i -> generate parent)
        let kb = persons @ parents

        let toTest = [1..10000] |> List.map (fun i -> generate (fun p c -> (GOAL "parent" [var p; var c])))

        toTest |> List.map (fun t -> solve t kb |> Seq.toList) |> ignore
    