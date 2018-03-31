namespace Solve

open TermTypes

open Rule
open Rule.Transformers
open VariableUnify

module ExpressionUnify =
    open VariableUnify

    let rec unifyCalc changeVariable calc =
        let rec changeCalcTermIfVariable =
            function
            | Value(VariableTerm(variableTerm)) -> Value(changeVariable variableTerm)
            | Value(TypedTerm(typedTerm)) -> Value(TypedTerm(typedTerm))
            | Value(StructureTerm(structureTerm)) -> Value(StructureTerm(changeVariablesForStruct changeVariable structureTerm))
            | _ as calc -> unifyCalc changeVariable calc
        match calc with
        | Plus (leftOp, rightOp) -> Plus(changeCalcTermIfVariable leftOp, changeCalcTermIfVariable rightOp)
        | Subsctruct (leftOp, rightOp) -> Subsctruct(changeCalcTermIfVariable leftOp, changeCalcTermIfVariable rightOp)
        | Multiply (leftOp, rightOp) -> Multiply(changeCalcTermIfVariable leftOp, changeCalcTermIfVariable rightOp)
        | Division (leftOp, rightOp) -> Division(changeCalcTermIfVariable leftOp, changeCalcTermIfVariable rightOp)
        | Invert (x) -> Invert(changeCalcTermIfVariable x)
        | Sqrt (x) -> Sqrt(changeCalcTermIfVariable x)
        | Log (x, s) -> Log(changeCalcTermIfVariable x, changeCalcTermIfVariable s)
        | Value(_) as value -> changeCalcTermIfVariable value

    let rec unifyExpression expression changeVariable =
        // TODO: check if there should be inner structure unification
        let postUnifyBinaryExpression (procVariableChange: Variable -> Term) (functor': Term * Term -> 'a) (leftTerm: Term) (rightTerm: Term) =
            match (leftTerm, rightTerm) with
            | (VariableTerm(leftVarTerm), VariableTerm(rightVarTerm)) -> functor'(procVariableChange leftVarTerm, procVariableChange rightVarTerm)
            | (VariableTerm(leftVarTerm), TypedTerm(_)) -> functor'(procVariableChange leftVarTerm, rightTerm)
            | (VariableTerm(leftVarTerm), StructureTerm(rightStructureTerm)) -> functor'(procVariableChange leftVarTerm, StructureTerm(changeVariablesForStruct procVariableChange rightStructureTerm))
            | (VariableTerm(leftVarTerm), ListTerm(rightListTerm)) -> functor'(procVariableChange leftVarTerm, ListTerm(changeVariablesForList procVariableChange rightListTerm))
            | (TypedTerm(_), VariableTerm(rightVarTerm)) -> functor'(leftTerm, procVariableChange rightVarTerm)
            | (StructureTerm(leftStructureTerm), VariableTerm(rightVarTerm)) -> functor'(StructureTerm(changeVariablesForStruct procVariableChange leftStructureTerm), procVariableChange rightVarTerm)
            | (ListTerm(leftListTerm), VariableTerm(rightVarTerm)) -> functor'(ListTerm(changeVariablesForList procVariableChange leftListTerm), procVariableChange rightVarTerm)
            | (ListTerm(leftListTerm), ListTerm(rightListTerm)) -> functor'(ListTerm(changeVariablesForList procVariableChange leftListTerm), ListTerm(changeVariablesForList procVariableChange rightListTerm))
            | _ -> functor'(leftTerm, rightTerm)

        match expression with
        | True -> True
        | False -> False
        | Cut -> Cut
        | NotExpression expr -> NotExpression (unifyExpression expr changeVariable)
        | OrExpression (leftExpr, rightExpr) -> OrExpression(unifyExpression leftExpr changeVariable, unifyExpression rightExpr changeVariable)
        | AndExpression (leftExpr, rightExpr) -> AndExpression(unifyExpression leftExpr changeVariable, unifyExpression rightExpr changeVariable)
        | ResultExpression expr ->
            match expr with
            | VariableTerm variableTerm -> ResultExpression (changeVariable variableTerm)
            | TypedTerm _ -> expression
            | StructureTerm structureTerm -> ResultExpression(StructureTerm(changeVariablesForStruct changeVariable structureTerm))
            | ListTerm listTerm -> ResultExpression(ListTerm(changeVariablesForList changeVariable listTerm))
        | CallExpression(GoalSignature(goalName, arguments)) ->
            let newGoalArgs =
                arguments
                |> fromArgs
                |> List.map (function
                            | VariableTerm(variableTerm) -> Argument(changeVariable variableTerm)
                            | TypedTerm(typedTerm) -> Argument(TypedTerm(typedTerm))
                            | StructureTerm(structureTerm) -> Argument(StructureTerm(changeVariablesForStruct changeVariable structureTerm))
                            | ListTerm(listTerm) -> Argument(ListTerm(changeVariablesForList changeVariable listTerm)))
            CallExpression (GoalSignature(goalName, newGoalArgs))
        | CalcExpr (calcTerm, calc) ->
            match calcTerm with
            | VariableTerm(variableTerm) -> CalcExpr(changeVariable variableTerm, unifyCalc changeVariable calc)
            | TypedTerm(typedTerm) -> CalcExpr(TypedTerm(typedTerm), unifyCalc changeVariable calc)
            | ListTerm _ -> failwith "Calc of list is not implemented yet"
            | StructureTerm _ -> failwith "Calc of custom struct is not implemented yet"
        | EqExpr (leftTerm, rightTerm) -> postUnifyBinaryExpression changeVariable EqExpr leftTerm rightTerm
        | GrExpr (leftTerm, rightTerm) -> postUnifyBinaryExpression changeVariable GrExpr leftTerm rightTerm
        | LeExpr (leftTerm, rightTerm) -> postUnifyBinaryExpression changeVariable LeExpr leftTerm rightTerm
        | _ -> failwith "unchecked something"

    // returns change variable functions according to execution branches
    let getChangedVariableFns initialExpression expression =
        /// There is a matching between t1 and t2 terms. After execution there could be changed variables that should be catched by every existing variable
        let backwardsTermUnification (leftTerm: Term) (rightTerm: Term) (procVarOtherChange: Variable -> Term) (variable: Variable) =
            match leftTerm with
            | VariableTerm(variableTerm) when variableTerm = variable -> rightTerm
            | _ -> procVarOtherChange variable
            
        let postUnifyBinaryExpressions ((leftFirstTerm, leftSecondTerm): Term * Term) ((rightFirstTerm, rightSecondTerm): Term * Term) (procVarOtherChange: Variable -> Term) (variable: Variable) =
            let postUnify (leftTerm: Term) (rightTerm: Term) (variable: Variable) =
                match leftTerm with
                | VariableTerm(variableTerm) when variableTerm = variable -> Some rightTerm
                | ListTerm(_) ->
                    let rec unifl leftList rightList = 
                        match leftList, rightList with
                        | NilTerm, NilTerm -> None
                        | VarListTerm(varListTerm), _ when varListTerm = variable -> Some (ListTerm(rightList))
                        | TypedListTerm(VariableTerm(leftVarTerm), _), TypedListTerm(rightVarTerm, _) when leftVarTerm = variable ->
                            Some rightVarTerm
                        | TypedListTerm(_, leftTail), TypedListTerm(_, rightTail) ->
                            unifl leftTail rightTail
                        | _ -> None

                    match leftTerm, rightTerm with
                    | ListTerm(leftListTerm), ListTerm(rightListTerm) -> unifl leftListTerm rightListTerm
                    | _ -> failwithf "Unable to unify list with not list %A, %A" leftTerm rightTerm
                | _ ->
                    match procVarOtherChange variable with
                    | VariableTerm(variableFromTerm) when variableFromTerm = variable -> None
                    | res -> Some res

            match postUnify leftFirstTerm rightFirstTerm variable with
            | Some resv -> resv
            | None ->
                match postUnify leftSecondTerm rightSecondTerm variable with
                | Some resv -> resv
                | _ -> procVarOtherChange variable
        
        let rec _getChangedVariableFn initialExpression expression (changedVariableFns: (Variable -> Term) list) =
            match (initialExpression, expression) with
            | (True, True) -> changedVariableFns
            | (False, False) -> changedVariableFns
            | (Cut, Cut) -> changedVariableFns
            | (_, NotExecuted _) -> changedVariableFns
            | (NotExpression leftExpr, NotExpression rightExpr) -> _getChangedVariableFn leftExpr rightExpr changedVariableFns
            | (OrExpression(leftFirstExpr, leftRightExpr), OrExpression(rightFirstExpr, rightSecondExpr)) ->
                let leftChangedVariable = _getChangedVariableFn leftFirstExpr rightFirstExpr changedVariableFns
                let rightChangedVariable = _getChangedVariableFn leftRightExpr rightSecondExpr changedVariableFns
                leftChangedVariable@rightChangedVariable
            | (AndExpression(leftFirstExpr, leftSecondExpr), AndExpression(rightFirstExpr, rightSecondExpr)) ->
                let leftChangedVariable = _getChangedVariableFn leftFirstExpr rightFirstExpr changedVariableFns
                let rightChangedVariable = _getChangedVariableFn leftSecondExpr rightSecondExpr leftChangedVariable
                rightChangedVariable
            | (ResultExpression leftExpr, ResultExpression rightExpr) -> changedVariableFns |> List.map (backwardsTermUnification leftExpr rightExpr)
            | (CallExpression(GoalSignature(leftName, leftArgs)), CallExpression(GoalSignature(rightName, rightArgs))) when leftName = rightName && leftArgs.Length = rightArgs.Length ->
                List.map (fun changeVariable -> List.fold2 (fun changeVariables leftArgument rightArgument -> backwardsTermUnification leftArgument rightArgument changeVariables) changeVariable (fromArgs leftArgs) (fromArgs rightArgs)) changedVariableFns
            | (CalcExpr(leftCalcTerm, _), CalcExpr(rightCalcTerm, _)) -> changedVariableFns |> List.map (backwardsTermUnification leftCalcTerm rightCalcTerm)
            | (EqExpr(leftFirstTerm, leftSecondTerm), EqExpr(rightFirstTerm, rightSecondTerm)) -> changedVariableFns |> List.map (postUnifyBinaryExpressions (leftFirstTerm, leftSecondTerm) (rightFirstTerm, rightSecondTerm))
            | (GrExpr(leftFirstTerm, leftSecondTerm), GrExpr(rightFirstTerm, rightSecondTerm)) -> changedVariableFns |> List.map (postUnifyBinaryExpressions (leftFirstTerm, leftSecondTerm) (rightFirstTerm, rightSecondTerm))
            | (LeExpr(leftFirstTerm, leftSecondTerm), LeExpr(rightFirstTerm, rightSecondTerm)) -> changedVariableFns |> List.map (postUnifyBinaryExpressions (leftFirstTerm, leftSecondTerm) (rightFirstTerm, rightSecondTerm))
            | _ -> failwithf "failed to getChangedVariableFn result. %O != %O" initialExpression expression
        _getChangedVariableFn initialExpression expression [VariableTerm]
        
    let unifyRule (Rule(Signature(name, parameters), body)) arguments =
        let unifyExpressionByParams parameters arguments expression =
            let changeVariable (Parameter(parameter)) argument =
                let retIfEquals variable result checkedVariable = if checkedVariable = variable then result else VariableTerm(checkedVariable)

                match (parameter, argument) with
                | VariableTerm(leftVariable), VariableTerm(rightVariable) -> fun checkedVariable -> if checkedVariable = rightVariable then VariableTerm leftVariable else VariableTerm checkedVariable
                | VariableTerm(leftVariable), _ -> retIfEquals leftVariable argument
                | _, VariableTerm(rightVariable) -> retIfEquals rightVariable parameter
                | _ -> VariableTerm

            unifyParametersWithArguments parameters arguments
            |> Option.bind (fun unifiedArgs ->
                let newExpr = 
                    List.zip parameters unifiedArgs
                    |> List.fold (fun acc (parameter, unifiedArg) -> unifyExpression acc (changeVariable parameter unifiedArg)) expression
                (newExpr, unifiedArgs)
                |> Some)

        unifyExpressionByParams parameters arguments body
        |> Option.bind (fun (resultBody, resultParameters) -> Some(Rule(Signature(name, toParams resultParameters), resultBody)))
    
    let rec unifyListTerms (leftListTerm: TypedListTerm) (rightListTerm: TypedListTerm): Term -> Term =
        match (leftListTerm, rightListTerm) with
        | NilTerm, NilTerm -> id
        | VarListTerm(varListTerm), rightListTerm -> fun v -> if v = VariableTerm(varListTerm) then ListTerm(rightListTerm) else v
        | TypedListTerm(leftTerm, leftTail), TypedListTerm(rightTerm, rightTail) ->
            fun variableTerm -> if variableTerm = leftTerm then rightTerm else unifyListTerms leftTail rightTail variableTerm
        | _ -> failwithf "Failed to unify two list terms %A, %A" leftListTerm rightListTerm

    let rec unifyResultToParameters arguments initialExpression expression =
        let unifyWithArgs (arguments: Term list) (left: Term) (right: Term) =
            arguments
            |> List.map (fun argument -> 
                match left, right with
                | _ when argument = left -> right
                | ListTerm(leftList), ListTerm(rightList) -> unifyListTerms leftList rightList argument
                | _ -> argument
            )

        match (initialExpression, expression) with
        | (True, True) -> arguments
        | (False, False) -> []
        | (Cut, Cut) -> arguments
        | (_, NotExecuted _) -> arguments
        | (NotExpression leftExpr, NotExpression rightExpr) -> unifyResultToParameters arguments leftExpr rightExpr
        | (OrExpression(leftFirstExpr, leftSecondExpr), OrExpression(rightFirstExpr, rightSecondExpr)) -> unifyResultToParameters (unifyResultToParameters arguments leftFirstExpr rightFirstExpr) leftSecondExpr rightSecondExpr
        | (AndExpression(leftFirstExpr, leftSecondExpr), AndExpression(rightFirstExpr, rightSecondExpr)) -> unifyResultToParameters (unifyResultToParameters arguments leftFirstExpr rightFirstExpr) leftSecondExpr rightSecondExpr
        | (ResultExpression leftExpr, ResultExpression rightExpr) -> arguments |> List.map (fun argument -> if argument = leftExpr then rightExpr else argument)
        | (CallExpression(GoalSignature(leftGoalName, leftArguments)), CallExpression(GoalSignature(rightGoalName, rightArguments))) when leftGoalName = rightGoalName && leftArguments.Length = rightArguments.Length ->
            List.fold2 (fun args (leftArgument) (rightArgument) -> unifyWithArgs args leftArgument rightArgument) arguments (fromArgs leftArguments) (fromArgs rightArguments)
        | (CalcExpr(leftTerm, _), CalcExpr(rightTerm, _)) -> unifyWithArgs arguments leftTerm rightTerm
        | (EqExpr(leftFirstExpr, leftSecondExpr), EqExpr(rightFirstExpr, rightSecondExpr)) -> unifyWithArgs (unifyWithArgs arguments leftFirstExpr rightFirstExpr) leftSecondExpr rightSecondExpr
        | (GrExpr(leftFirstExpr, leftSecondExpr), GrExpr(rightFirstExpr, rightSecondExpr)) -> unifyWithArgs (unifyWithArgs arguments leftFirstExpr rightFirstExpr) leftSecondExpr rightSecondExpr
        | (LeExpr(leftFirstExpr, leftSecondExpr), LeExpr(rightFirstExpr, rightSecondExpr)) -> unifyWithArgs (unifyWithArgs arguments leftFirstExpr rightFirstExpr) leftSecondExpr rightSecondExpr
        | _ -> failwithf "failed to unify result. %O != %O" initialExpression expression