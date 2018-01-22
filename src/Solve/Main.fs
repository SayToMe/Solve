namespace Solve

open TermTypes

open Rule
open Rule.Transformers

open VariableUnify
open Execute

module Solve =
    let private checkAppliable (Goal(Structure(name, goalArguments))) (Rule(Signature(ruleName, ruleParams), _)) =
        name = ruleName && Option.isSome(unifyParamsWithArguments ruleParams (toArgs goalArguments))

    let rec solve (goal: Goal) (knowledgeBase: Rule list) =
        knowledgeBase
        |> List.filter (checkAppliable goal)
        |> List.toSeq
        |> Seq.collect (fun r ->
            execute goal r (fun custom -> solve custom knowledgeBase)
        )

