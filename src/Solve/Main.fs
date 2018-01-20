namespace Solve

open TermTypes
open TermTypes.Transformers

open Rule
open Rule.Transformers

open VariableUnify
open Execute

module Solve =
    let checkAppliable (Goal(Structure(name, goalArguments))) (Rule(Signature(ruleName, ruleParams), _)) =
        name = ruleName && Option.isSome(unifyParamsWithArguments ruleParams (toArgs goalArguments))

    let rec solve goal knowledgeBase =
        knowledgeBase
        |> List.filter (checkAppliable goal)
        |> List.toSeq
        |> Seq.collect (fun r ->
            execute goal r (fun custom -> solve custom knowledgeBase)
        )

