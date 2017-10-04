namespace Solve

open TermTypes
open TermTypes.Transformers

open Rule
open Rule.Transformers

open VariableUnify
open Execute

module Solve =
    let rec solve goal knowledgeBase =
        let checkAppliable (Goal(Structure(name, goalArguments))) (Rule(Signature(ruleName, ruleParams), _)) =
            let arguments = toArgs goalArguments
            name = ruleName && Option.isSome(unifyParamsWithArguments ruleParams arguments)

        knowledgeBase
        |> List.filter (checkAppliable goal)
        |> List.toSeq
        |> Seq.collect (fun r ->
            execute goal r (fun custom -> solve custom knowledgeBase)
        )