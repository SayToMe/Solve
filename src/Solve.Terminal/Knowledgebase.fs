namespace Solve.Terminal

open Solve
open Rule
open Rule.Transformers
open TermTypes

open Solve.PrologParser
open Solve.PrologParser.Primitives
open Solve.PrologParser.Parser

type IKnowledgebaseWrapper =
    abstract member AddRule: Rule -> unit
    abstract member Solve: Goal -> string seq
   
type MutableKnowledgebase(initialKnowledgebase: Rule list) =
    let mutable innerKnowledgebase = initialKnowledgebase

    interface IKnowledgebaseWrapper with
        member __.AddRule rule =
            innerKnowledgebase <- innerKnowledgebase @ [rule]

        member __.Solve (Goal(goal)) =
            Solve.solve goal innerKnowledgebase
            |> Seq.map (fun result ->
                result
                |> List.fold (fun acc (v, t) ->
                    let str = (VariableTerm(v).AsString + " = " + t.AsString)
                    if String.length acc = 0 then
                        str
                    else
                        acc + ", " + str
                ) ""
            )
