namespace Solve.Tests
open NUnit.Framework

open Solve

open TermTypes
open TermTypes.Transformers

open Rule

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
    let ``Given ontology solve with person('Polina') should return true``() =
        solve (GOAL "person" [stringList "Polina"]) knowledgebase
        |> checkSolve [[]]
        
    [<Test>]
    let ``Given ontology solve with person('Miwa') should return false``() =
        solve (GOAL "person" [stringList "Miwa"]) knowledgebase
        |> checkSolve []

    [<Test>]
    let ``Given ontology solve with person(X) should return all people``() =
        solve (GOAL "person" [var "X"]) knowledgebase
        |> checkSolve [[Variable "X", stringList "Mary"]; [Variable "X", stringList "Polina"]; [Variable "X", stringList "Evgeniy"]; [Variable "X", stringList "Solniwko"]]

    [<Test>]
    let ``Given ontology solve with parent('Polina', Descendant) should return [Descendant = 'Evgeniy']``() =
        solve (GOAL "parent" [stringList "Polina"; var "Descendant"]) knowledgebase
        |> checkSolve [[Variable "Descendant",  stringList "Evgeniy"]]

    [<Test>]
    let ``Given ontology solve with parent(Parent, Descendant) should return all parents``() =
        solve (GOAL "parent" [var "Parent"; var "Descendant"]) knowledgebase
        |> checkSolve [[Variable "Parent", stringList "Mary"; Variable "Descendant", stringList "Polina"]; [Variable "Parent", stringList "Solniwko"; Variable "Descendant", stringList "Polina"]; [Variable "Parent", stringList "Polina"; Variable "Descendant", stringList "Evgeniy"]]
        
    [<Test>]
    let ``Given `ontology and biparent_person_first` solve with biparent_person_first(Parent, Descendant) should return something``() =
        let biparent_pf = RULE(SIGNATURE "biparent_person_first" [var "P"; var "C"]) (AndExpression(GOAL "person" [var "P"], (AndExpression(GOAL "person" [var "C"], GOAL "parent" [var "P"; var "C"]))))
        let knowledgebase = knowledgebase@[biparent_pf]
        
        solve (GOAL "biparent_person_first" [var "Parent"; var "Descendant"]) knowledgebase
        |> checkSolve [[Variable "Parent", stringList "Mary"; Variable "Descendant", stringList "Polina"]; [Variable "Parent", stringList "Polina"; Variable "Descendant", stringList "Evgeniy"]; [Variable "Parent", stringList "Solniwko"; Variable "Descendant", stringList "Polina"]]
        
    [<Test>]
    let ``Given `ontology and biparent_person_last` solve with biparent_person_last(Parent, Descendant) should return something``() =
        let biparent_pl = RULE(SIGNATURE "biparent_person_last" [var "P"; var "C"]) (AndExpression(GOAL "parent" [var "P"; var "C"], AndExpression(GOAL "person" [var "P"], GOAL "person" [var "C"])))
        let knowledgebase = knowledgebase@[biparent_pl]
        
        solve (GOAL "biparent_person_last" [var "Parent"; var "Descendant"]) knowledgebase
        |> checkSolve [[Variable "Parent", stringList "Mary"; Variable "Descendant", stringList "Polina"]; [Variable "Parent", stringList "Solniwko"; Variable "Descendant", stringList "Polina"]; [Variable "Parent", stringList "Polina"; Variable "Descendant", stringList "Evgeniy"]]
        
    [<Test>]
    let ``Given ontology solve with notParent(NotParent) should return [NotParent = 'Evgeniy']``() =
        solve (GOAL "notParent" [var "NotParent"]) knowledgebase
        |> checkSolve [[Variable "NotParent", stringList "Evgeniy"]]

    [<Test>]
    let ``Given ontology solve with notParent('Mary') should return false``() =
        solve (GOAL "notParent" [stringList "Mary"]) knowledgebase
        |> checkSolve []

    [<Test>]
    let ``Given ontology solve with grandparent(GrandParent, Descendant) should return something``() =
        solve (GOAL "grandparent" [var "GrandParent"; var "Descendant"]) knowledgebase
        |> checkSolve [[Variable "GrandParent", stringList "Mary"; Variable "Descendant", stringList "Evgeniy"]; [Variable "GrandParent", stringList "Solniwko"; Variable "Descendant", stringList "Evgeniy"]]

    [<Test>]
    let ``Given ontology solve with grandparent('Mary', 'Evgeniy') should return true``() =
        solve (GOAL "grandparent" [stringList "Mary"; stringList "Evgeniy"]) knowledgebase
        |> checkSolve [[]]
