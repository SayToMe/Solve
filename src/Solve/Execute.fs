namespace Solve

open TermTypes

open Rule
open Rule.Transformers

open VariableUnify
open ExpressionUnify

module Execute =
    let rec executeCalc (calc: Calc) =
        let getCalcInnerNumber =
            function
            | Value (TypedTerm(TypedNumberTerm(x))) -> x
            | _ as inner -> executeCalc inner
        let getMonoOpInnerNumber (op: double -> double) (calc: Calc) =
            let (NumberTerm(number)) = getCalcInnerNumber calc
            NumberTerm(op number)
        let getBiectiveOpInnerNumber (op: double -> double -> double) (leftCalc: Calc) (rightCalc: Calc) =
            let (NumberTerm(leftNumber)) = getCalcInnerNumber leftCalc
            let (NumberTerm(rightNumber)) = getCalcInnerNumber rightCalc
            NumberTerm(op leftNumber rightNumber)
        let safeDivision x y =
            if y = 0. then
                nan
            else
                x / y

        match calc with
        | Value (TypedTerm(TypedNumberTerm(NumberTerm number))) -> NumberTerm number
        | Value (StructureTerm(Structure(functor', arguments))) ->
            match functor' with
            | "+" when arguments.Length = 2 -> executeCalc (Plus(Value(arguments.[0]), Value(arguments.[1])))
            | "-" when arguments.Length = 2 -> executeCalc (Subsctruct(Value(arguments.[0]), Value(arguments.[1])))
            | "*" when arguments.Length = 2 -> executeCalc (Multiply(Value(arguments.[0]), Value(arguments.[1])))
            | "/" when arguments.Length = 2 -> executeCalc (Division(Value(arguments.[0]), Value(arguments.[1])))
            | "-" when arguments.Length = 1 -> executeCalc (Invert(Value(arguments.[0])))
            | "sqrt" when arguments.Length = 1 -> executeCalc (Sqrt(Value(arguments.[0])))
            | "log" when arguments.Length = 2 -> executeCalc (Log(Value(arguments.[0]), Value(arguments.[1])))
            | _ as c -> failwithf "Cant find according calc functor'. %A" c
        | Plus (leftCalc, rightCalc) -> getBiectiveOpInnerNumber (+) leftCalc rightCalc
        | Subsctruct (leftCalc, rightCalc) -> getBiectiveOpInnerNumber (-) leftCalc rightCalc
        | Multiply (leftCalc, rightCalc) -> getBiectiveOpInnerNumber (*) leftCalc rightCalc
        | Division (leftCalc, rightCalc) -> getBiectiveOpInnerNumber safeDivision leftCalc rightCalc
        | Invert (calc) -> getMonoOpInnerNumber (~-) calc
        | Sqrt (calc) -> getMonoOpInnerNumber System.Math.Sqrt calc
        | Log (leftCalc, rightCalc) -> getBiectiveOpInnerNumber (fun v n -> System.Math.Log(v, n)) leftCalc rightCalc
        | _ as c -> failwithf "incorrect calc expression called. %A" c

    // TODO: maybe we should unify each time we execute expression?
    // IDEA IS:
    // rewrite as search for goal(Expression)
    // no execute custom, that should be accessible by knowledgebase right here probably
    // no change variable fn, goal is unified right there
    let rec executeExpression (expr: Expression) (executeCustom: GoalSignature -> #seq<Term list>) (changeVariableFn: Variable -> Term) =
        let keepOnlyFirstCut exprs =
            let rec exprHasCut expr =
                match expr with
                | Cut -> true
                | AndExpression(leftExpr, rightExpr) -> exprHasCut leftExpr || exprHasCut rightExpr
                | OrExpression(leftExpr, rightExpr) -> exprHasCut leftExpr || exprHasCut rightExpr
                | NotExpression(expr) -> exprHasCut expr
                | _ -> false

            Seq.unfold (fun seq ->
                if Seq.isEmpty seq then
                    None
                else
                    let head = Seq.head seq
                    let tail = Seq.tail seq

                    if exprHasCut head then
                        Some(head, Seq.empty)
                    else
                        Some(head, tail)
            ) exprs

        let changeIfVariable changeVariable =
            function
            | VariableTerm(variable) -> changeVariable variable
            | term -> term
            
        // TODO check structure execute is correct
        let rec executeMap (condition: TypedTerm -> TypedTerm -> bool) (leftTerm: Term) (rightTerm: Term): (Term * Term) seq =
            // Hack for equality check
            let conditionIsEquality = condition (TypedNumberTerm(NumberTerm(1.))) (TypedNumberTerm(NumberTerm(1.)))

            let leftTerm = changeIfVariable changeVariableFn leftTerm
            let rightTerm = changeIfVariable changeVariableFn rightTerm
            match (leftTerm, rightTerm) with
            | (VariableTerm(_), VariableTerm(_)) -> Seq.singleton (rightTerm, rightTerm)
            | (VariableTerm(_), TypedTerm(_)) -> Seq.singleton (rightTerm, rightTerm)
            | (VariableTerm(_), StructureTerm(_)) -> Seq.singleton (rightTerm, rightTerm)
            | (VariableTerm(_), ListTerm(_)) -> Seq.singleton (rightTerm, rightTerm)
            | (TypedTerm(_), VariableTerm(_)) -> Seq.singleton (leftTerm, leftTerm)
            | (StructureTerm(_), VariableTerm(_)) -> Seq.singleton (leftTerm, leftTerm)
            | (ListTerm(_), VariableTerm(_)) -> Seq.singleton (leftTerm, leftTerm)
            | (TypedTerm(leftTypedTerm), TypedTerm(rightTypedTerm)) ->
                if condition leftTypedTerm rightTypedTerm then
                    Seq.singleton (leftTerm, rightTerm)
                else
                    Seq.empty
            | (StructureTerm(leftStructureTerm), StructureTerm(rightStructureTerm)) ->
                if conditionIsEquality && leftStructureTerm = rightStructureTerm then
                    Seq.singleton (leftTerm, rightTerm)
                else
                    Seq.empty
            | (ListTerm leftListTerm, ListTerm rightListTerm) ->
                let rec procListChangedVariable leftList rightList =
                    match leftList, rightList with
                    | NilTerm, NilTerm -> Seq.singleton (NilTerm, NilTerm)
                    | VarListTerm _, _ -> Seq.singleton (rightList, rightList)
                    | _, VarListTerm _ -> Seq.singleton (leftList, leftList)
                    | TypedListTerm(leftTerm, leftTail), TypedListTerm(rightTerm, rightTail) ->
                        let leftTerm = changeIfVariable changeVariableFn leftTerm
                        let rightTerm = changeIfVariable changeVariableFn rightTerm

                        let unift = executeMap condition leftTerm rightTerm

                        unift
                        |> Seq.map fst
                        |> Seq.collect (fun term -> 
                            procListChangedVariable leftTail rightTail
                            |> Seq.map (fun (leftTail, rightTail) -> 
                                (TypedListTerm(term, leftTail), TypedListTerm(term, rightTail))
                            )
                        )
                    | _ -> Seq.empty
                procListChangedVariable leftListTerm rightListTerm
                |> Seq.map (fun (leftListTerm, rightListTerm) -> ListTerm(leftListTerm), ListTerm(rightListTerm))
            | _ -> failwithf "Unexpected execute binary expression arguments %A, %A" leftTerm rightTerm

        let rec executeBinaryExpression (functor': Term * Term -> Expression) (condition: TypedTerm -> TypedTerm -> bool) (leftTerm: Term) (rightTerm: Term): Expression seq =
            executeMap condition leftTerm rightTerm |> Seq.map functor'
        
        match expr with
        | True -> Seq.singleton True
        | False -> Seq.empty
        | Cut -> Seq.singleton Cut
        | NotExpression expr ->
            let executed = executeExpression (AndExpression(Cut, expr)) executeCustom changeVariableFn
            if Seq.isEmpty executed then
                Seq.singleton (NotExpression expr)
            else
                Seq.empty
        | OrExpression (leftExpr, rightExpr) ->
            let first = executeExpression leftExpr executeCustom changeVariableFn |> Seq.map (fun v -> OrExpression(v, NotExecuted rightExpr))
            let second = (executeExpression rightExpr executeCustom changeVariableFn |> Seq.map (fun x -> OrExpression(NotExecuted leftExpr, x)))

            Seq.append first second |> keepOnlyFirstCut
        | AndExpression (leftExpr, rightExpr) ->
            let executedExpressionResults = executeExpression leftExpr executeCustom changeVariableFn

            match rightExpr with
            | Cut -> Seq.truncate 1 executedExpressionResults |> Seq.map (fun leftExprResult -> AndExpression(leftExprResult, rightExpr))
            | _ ->
                executedExpressionResults
                |> Seq.collect (fun executedLeftExprRes ->
                    let tofixChangedVariablesResults =  getChangedVariableFns leftExpr executedLeftExprRes

                    tofixChangedVariablesResults
                    |> Seq.collect (fun changeVariables ->
                        let changedExpression = unifyExpression rightExpr changeVariables
                        let toFixChangedVariablesResult = getChangedVariableFns rightExpr changedExpression

                        toFixChangedVariablesResult
                        |> Seq.collect (fun fn ->
                            executeExpression changedExpression executeCustom fn
                            |> Seq.map (fun executedRightExprRes -> AndExpression(executedLeftExprRes, executedRightExprRes))
                        )
                    )
                )
        | ResultExpression expr -> Seq.singleton (ResultExpression expr)
        | CallExpression (GoalSignature(name, args)) ->
            executeCustom (GoalSignature(name, args))
            |> Seq.map (fun resTerms -> CallExpression(GoalSignature(name, toArgs resTerms)))
        | CalcExpr (term, calc) ->
            let changedTerm = changeIfVariable changeVariableFn term
            let calc = unifyCalc changeVariableFn calc
            match changedTerm with
            | VariableTerm(_) -> Seq.singleton (CalcExpr(TypedTerm(TypedNumberTerm(executeCalc calc)), calc))
            | TypedTerm(TypedNumberTerm(number)) when number = (executeCalc calc) -> Seq.singleton (CalcExpr(TypedTerm(TypedNumberTerm(number)), calc))
            | _ -> Seq.empty
        | EqExpr (leftExpr, rightExpr) -> executeBinaryExpression EqExpr (=) leftExpr rightExpr
        | GrExpr (leftExpr, rightExpr) -> executeBinaryExpression GrExpr (>) leftExpr rightExpr
        | LeExpr (leftExpr, rightExpr) -> executeBinaryExpression LeExpr (<) leftExpr rightExpr
        | _ -> Seq.empty
    
    let getExpressionVariables expr =
        let rec getVariablesFromTerm term =
            match term with
            | VariableTerm(variable) -> [variable]
            | StructureTerm(Structure(_, terms)) -> terms |> List.collect getVariablesFromTerm
            | ListTerm(listTerm) -> 
                match listTerm with
                | NilTerm -> []
                | VarListTerm(varListTerm) -> [varListTerm]
                | TypedListTerm(term, listTail) ->
                    match term with
                    | VariableTerm(variableTerm) -> [variableTerm] @ getVariablesFromTerm (ListTerm(listTail))
                    | _ -> getVariablesFromTerm (ListTerm(listTail))
            | _ -> []

        let rec getExprVariables expr =
            match expr with
            | True -> []
            | False -> []
            | Cut -> []
            | NotExpression expr -> getExprVariables expr
            | OrExpression (leftExpr, rightExpr) -> getExprVariables leftExpr @ getExprVariables rightExpr
            | AndExpression (leftExpr, rightExpr) -> getExprVariables leftExpr @ getExprVariables rightExpr
            | ResultExpression t -> getVariablesFromTerm t
            | CallExpression (GoalSignature(_, args)) -> args |> fromArgs |> List.collect getVariablesFromTerm
            | CalcExpr (v, _) -> getVariablesFromTerm v
            | EqExpr (leftTerm, rightTerm) -> getVariablesFromTerm leftTerm @ getVariablesFromTerm rightTerm
            | GrExpr (leftTerm, rightTerm) -> getVariablesFromTerm leftTerm @ getVariablesFromTerm rightTerm
            | LeExpr (leftTerm, rightTerm) -> getVariablesFromTerm leftTerm @ getVariablesFromTerm rightTerm
            | _ -> []
        getExprVariables expr
        |> List.distinct
        
    // Assumption: expressions are the same
    let getExpressionVariableValues expr resexpr =
        let rec getVariableValueFromTerm (term: Term) (resultTerm: Term) =
            match term with
            | VariableTerm(variable) -> [(variable, resultTerm)]
            | StructureTerm(Structure(_, terms)) ->
                match resultTerm with
                | StructureTerm(Structure(_, resterms)) when terms.Length = resterms.Length ->
                    (terms, resterms)
                    ||> List.map2 (fun leftTerm rightTerm -> getVariableValueFromTerm leftTerm rightTerm)
                    |> List.collect id
                | StructureTerm(Structure(_, resultTerms)) when terms.Length <> resultTerms.Length ->
                    failwith "Structure term could be unified only with structure term of same arity"
                | _ -> failwith "Structure term can't be unified with anything by structure term"
            | ListTerm(listTerm) ->
                match resultTerm with
                | ListTerm(resultListTerm) ->
                    match listTerm, resultListTerm with
                    | NilTerm, NilTerm -> []
                    | VarListTerm(variable), valt -> [(variable, ListTerm(valt))]
                    | TypedListTerm(term, tail), TypedListTerm(t1, tail1) ->
                        match term with
                        | VariableTerm(variable) -> [(variable, t1)] @ getVariableValueFromTerm (ListTerm tail) (ListTerm tail1)
                        | _ -> getVariableValueFromTerm (ListTerm tail) (ListTerm tail1)
                    | _ -> failwith "Incorrectly defined term/resterm"
                | _ -> failwith "List term can't be unified with anything but list term"
            | _ -> []

        let rec getExprVariables expr resexpr =
            match expr, resexpr with
            | True, True -> []
            | False, False -> []
            | Cut, Cut -> []
            | NotExpression _, NotExpression _ -> []
            | _, NotExecuted _ -> []
            | NotExecuted _, _ -> []
            | OrExpression (leftFirstExpr, leftSecondExpr), OrExpression (rightFirstExpr, rightSecondExpr) ->
                getExprVariables leftFirstExpr rightFirstExpr @ getExprVariables leftSecondExpr rightSecondExpr
            | AndExpression (leftFirstExpr, leftSecondExpr), AndExpression (rightFirstExpr, rightSecondExpr)  ->
                getExprVariables leftFirstExpr rightFirstExpr @ getExprVariables leftSecondExpr rightSecondExpr
            | ResultExpression leftTerm, ResultExpression rightTerm -> getVariableValueFromTerm leftTerm rightTerm
            | CallExpression (GoalSignature(name, args)), CallExpression (GoalSignature(name', args')) when name = name' && args.Length = args'.Length ->
                (fromArgs args, fromArgs args') ||> List.map2 (fun a a' -> getVariableValueFromTerm a a') |> List.collect (fun x -> x)
            | CalcExpr (leftTerm, _), CalcExpr (rightTerm, _) ->
                getVariableValueFromTerm leftTerm rightTerm
            | EqExpr (leftFirstTerm, leftSecondTerm), EqExpr (rightFirstTerm, rightSecondTerm) -> getVariableValueFromTerm leftFirstTerm rightFirstTerm @ getVariableValueFromTerm leftSecondTerm rightSecondTerm
            | GrExpr (leftFirstTerm, leftSecondTerm), GrExpr (rightFirstTerm, rightSecondTerm) -> getVariableValueFromTerm leftFirstTerm rightFirstTerm @ getVariableValueFromTerm leftSecondTerm rightSecondTerm
            | LeExpr (leftFirstTerm, leftSecondTerm), LeExpr (rightFirstTerm, rightSecondTerm) -> getVariableValueFromTerm leftFirstTerm rightFirstTerm @ getVariableValueFromTerm leftSecondTerm rightSecondTerm
            | _ -> failwithf "Failed to retrieve variables from %A to %A" expr resexpr
        getExprVariables expr resexpr
        |> List.distinct
        |> List.filter (fun variableTermPair ->
            match variableTermPair with
            | (variable, VariableTerm(variableTerm)) when variable = variableTerm -> false
            | (variable, ListTerm(VarListTerm(variableListTerm))) when variable = variableListTerm -> false
            | _ -> true
        )

    let postExecuteUnify fromArgs resArgs =
        fromArgs
        |> Seq.map (fun terms ->
            let rec procList leftList rightList =
                match leftList, rightList with
                | NilTerm, NilTerm -> NilTerm
                | VarListTerm(leftVariable), VarListTerm(_) -> VarListTerm(leftVariable)
                | VarListTerm(_), rightTerm -> rightTerm
                | leftTerm, VarListTerm(_) -> leftTerm
                | TypedListTerm(leftTerm, leftTail), TypedListTerm(rightTerm, rightTail) ->
                    match leftTerm, rightTerm with
                    | VariableTerm(_), VariableTerm(_) -> TypedListTerm(rightTerm, procList leftTail rightTail)
                    | _ -> TypedListTerm(rightTerm, procList leftTail rightTail)
                | _ -> failwithf "Unable to proceed post execution unification for lists %A, %A" leftList rightList

            let resultPostUnification =
                (terms, resArgs)
                ||> List.map2 (fun leftTerm argumentTerm ->
                    match leftTerm, argumentTerm with
                    | VariableTerm(_), VariableTerm(_) -> (leftTerm, argumentTerm)
                    | ListTerm(leftList), ListTerm(rightList) -> (leftTerm, ListTerm(procList leftList rightList))
                    | _ -> (leftTerm, leftTerm)
                )

            (terms)
            |> List.map (fun (term) -> 
                let (_, resultTerm) = List.find (fun (initialTerm, _) -> initialTerm = term) resultPostUnification
                resultTerm
            )
        )

    // Idea is:
    // Expression is unified with arguments by parameters
    // Expression executes and all variables are resolved
    // Expression tree should be mostly unchanged
    // All changed variables can be caught afterwards
    let executeCustomExpression (Goal(expr)) (executeCustom: GoalSignature -> #seq<Term list>): ((Variable * Term) list) seq =
        executeExpression expr executeCustom VariableTerm
        |> Seq.map (getExpressionVariableValues expr)

    let exExpr (expr: Expression) (executeCustom: GoalSignature -> #seq<Term list>) (changeVariableFn: Variable -> Term): ((Variable * Term) list) seq =
        executeExpression expr executeCustom changeVariableFn
        |> Seq.map (getExpressionVariableValues expr)