namespace Solve

open Rule

open VariableUnify
open Execute

module Main =
    let checkApply (Goal(name, arguments)) (Rule(Signature(ruleName, ruleParams), _)) =
        name = ruleName && Option.isSome(unifyParamsWithArguments ruleParams arguments)

    let rec checkGoal goal knowledgeBase =
        knowledgeBase
        |> List.filter (checkApply goal)
        |> List.collect (fun r ->
            execute goal r (fun custom -> checkGoal custom knowledgeBase)
        )