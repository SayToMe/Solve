namespace Solve

open Types
open Types.Transformers

open Rule
open Rule.Transformers

open VariableUnify
open Execute

module Solve =
    let rec solve goal knowledgeBase =
        let checkAppliable goal (Rule(Signature(ruleName, ruleParams), _)) =
            let (Goal(Struct(name, goalArguments))) = goal
            let arguments = toArgs goalArguments
            name = ruleName && Option.isSome(unifyParamsWithArguments ruleParams arguments)

        knowledgeBase
        |> List.filter (checkAppliable goal)
        |> List.collect (fun r ->
            execute goal r (fun custom -> solve custom knowledgeBase)
        )