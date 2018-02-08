namespace Solve

open TermTypes

open Rule
open Rule.Transformers
open VariableUnify

module ExpressionUnify =
    open VariableUnify

    let rec unifyCalc changeVariable v =
        let rec changeCalcTermIfVariable =
            function
            | Value(VariableTerm(v)) -> Value(changeVariable v)
            | Value(TypedTerm(v)) -> Value(TypedTerm(v))
            | Value(StructureTerm(v)) -> Value(StructureTerm(changeVariablesForStruct changeVariable v))
            | _ as c -> unifyCalc changeVariable c
        match v with
        | Plus (v1, v2) -> Plus(changeCalcTermIfVariable v1, changeCalcTermIfVariable v2)
        | Subsctruct (v1, v2) -> Subsctruct(changeCalcTermIfVariable v1, changeCalcTermIfVariable v2)
        | Multiply (v1, v2) -> Multiply(changeCalcTermIfVariable v1, changeCalcTermIfVariable v2)
        | Division (v1, v2) -> Division(changeCalcTermIfVariable v1, changeCalcTermIfVariable v2)
        | Invert (v1) -> Invert(changeCalcTermIfVariable v1)
        | Sqrt (v1) -> Sqrt(changeCalcTermIfVariable v1)
        | Log (v1, n) -> Log(changeCalcTermIfVariable v1, changeCalcTermIfVariable n)
        | Value(_) as self -> changeCalcTermIfVariable self

    let rec unifyExpression expression changeVariable =
        // TODO: check if there should be inner structure unification
        let postUnifyBinaryExpression (proc: Variable -> Term) (functor': Term * Term -> 'a) (t1: Term) (t2: Term) =
            match (t1, t2) with
            | (VariableTerm(v1), VariableTerm(v2)) -> functor'(proc v1, proc v2)
            | (VariableTerm(v1), TypedTerm(_)) -> functor'(proc v1, t2)
            | (VariableTerm(v1), StructureTerm(v2)) -> functor'(proc v1, StructureTerm(changeVariablesForStruct proc v2))
            | (VariableTerm(v1), ListTerm(v2)) -> functor'(proc v1, ListTerm(changeVariablesForList proc v2))
            | (TypedTerm(_), VariableTerm(v2)) -> functor'(t1, proc v2)
            | (StructureTerm(v1), VariableTerm(v2)) -> functor'(StructureTerm(changeVariablesForStruct proc v1), proc v2)
            | (ListTerm(v1), VariableTerm(v2)) -> functor'(ListTerm(changeVariablesForList proc v1), proc v2)
            | (ListTerm(l1), ListTerm(l2)) -> functor'(ListTerm(changeVariablesForList proc l1), ListTerm(changeVariablesForList proc l2))
            | _ -> functor'(t1, t2)

        match expression with
        | True -> True
        | False -> False
        | Cut -> Cut
        | NotExpression e -> NotExpression (unifyExpression e changeVariable)
        | OrExpression (e1, e2) -> OrExpression(unifyExpression e1 changeVariable, unifyExpression e2 changeVariable)
        | AndExpression (e1, e2) -> AndExpression(unifyExpression e1 changeVariable, unifyExpression e2 changeVariable)
        | ResultExpression e ->
            match e with
            | VariableTerm v -> ResultExpression (changeVariable v)
            | TypedTerm _ -> expression
            | StructureTerm(v) -> ResultExpression(StructureTerm(changeVariablesForStruct changeVariable v))
            | ListTerm v -> ResultExpression(ListTerm(changeVariablesForList changeVariable v))
        | CallExpression(GoalSignature(goalName, arguments)) ->
            let newGoalArgs =
                arguments
                |> fromArgs
                |> List.map (function
                            | VariableTerm(v) -> Argument(changeVariable v)
                            | TypedTerm(v) -> Argument(TypedTerm(v))
                            | StructureTerm(v) -> Argument(StructureTerm(changeVariablesForStruct changeVariable v))
                            | ListTerm(v) -> Argument(ListTerm(changeVariablesForList changeVariable v)))
            CallExpression (GoalSignature(goalName, newGoalArgs))
        | CalcExpr (v, c) ->
            match v with
            | VariableTerm(vv) -> CalcExpr(changeVariable vv, unifyCalc changeVariable c)
            | TypedTerm(v) -> CalcExpr(TypedTerm(v), unifyCalc changeVariable c)
            | ListTerm _ -> failwith "Calc of list is not implemented yet"
            | StructureTerm _ -> failwith "Calc of custom struct is not implemented yet"
        | EqExpr (e1, e2) -> postUnifyBinaryExpression changeVariable EqExpr e1 e2
        | GrExpr (e1, e2) -> postUnifyBinaryExpression changeVariable GrExpr e1 e2
        | LeExpr (e1, e2) -> postUnifyBinaryExpression changeVariable LeExpr e1 e2
        | _ -> failwith "unchecked something"

    // returns change variable functions according to execution branches
    let getChangedVariableFns initialExpression expression =
        /// There is a matching between t1 and t2 terms. After execution there could be changed variables that should be catched by every existing variable
        let backwardsTermUnification (t1: Term) (t2: Term) (fn: Variable -> Term) (v: Variable) =
            match t1 with
            | VariableTerm(v1) when v1 = v -> t2
            | _ -> fn v
            
        let postUnifyBinaryExpressions ((t1, t2): Term * Term) ((t3, t4): Term * Term) (fn: Variable -> Term) (v: Variable) =
            if VariableTerm(v) = t1 then
                t3 
            else if VariableTerm(v) = t2 then 
                t4 
            else fn v
        
        let rec _getChangedVariableFn initialExpression expression (changedVariableFns: (Variable -> Term) list) =
            match (initialExpression, expression) with
            | (True, True) -> changedVariableFns
            | (False, False) -> changedVariableFns
            | (Cut, Cut) -> changedVariableFns
            | (_, NotExecuted _) -> changedVariableFns
            | (NotExpression e1, NotExpression e2) -> _getChangedVariableFn e1 e2 changedVariableFns
            | (OrExpression(e1, e2), OrExpression(e3, e4)) ->
                let changedFn1 = _getChangedVariableFn e1 e3 changedVariableFns
                let changedFn2 = _getChangedVariableFn e2 e4 changedVariableFns
                changedFn1@changedFn2
            | (AndExpression(e1, e2), AndExpression(e3, e4)) ->
                let changedFn1 = _getChangedVariableFn e1 e3 changedVariableFns
                let changedFn2 = _getChangedVariableFn e2 e4 changedFn1
                changedFn2
            | (ResultExpression e1, ResultExpression e2) -> changedVariableFns |> List.map (backwardsTermUnification e1 e2)
            | (CallExpression(GoalSignature(name1, goalArgs1)), CallExpression(GoalSignature(name2, goalArgs2))) when name1 = name2 && goalArgs1.Length = goalArgs2.Length ->
                List.map (fun fn -> List.fold2 (fun fns a1 a2 -> backwardsTermUnification a1 a2 fns) fn (fromArgs goalArgs1) (fromArgs goalArgs2)) changedVariableFns
            | (CalcExpr(v1, _), CalcExpr(v2, _)) -> changedVariableFns |> List.map (backwardsTermUnification v1 v2)
            | (EqExpr(v1, v2), EqExpr(v3, v4)) -> changedVariableFns |> List.map (postUnifyBinaryExpressions (v1, v2) (v3, v4))
            | (GrExpr(v1, v2), GrExpr(v3, v4)) -> changedVariableFns |> List.map (postUnifyBinaryExpressions (v1, v2) (v3, v4))
            | (LeExpr(v1, v2), LeExpr(v3, v4)) -> changedVariableFns |> List.map (postUnifyBinaryExpressions (v1, v2) (v3, v4))
            | _ -> failwithf "failed to getChangedVariableFn result. %O != %O" initialExpression expression
        _getChangedVariableFn initialExpression expression [(fun v -> VariableTerm(v))]
        
    let unifyRule (Rule(Signature(name, parameters), body)) arguments =
        let unifyExpressionByParams parameters arguments expression =
            let changeVariable (Parameter(p)) a =
                let retIfEquals variable result v = if v = variable then result else VariableTerm(v)

                match (p, a) with
                | VariableTerm(v1), VariableTerm(v2) -> fun v -> if v = v2 then VariableTerm v1 else VariableTerm v
                | VariableTerm(v1), _ -> retIfEquals v1 a
                | _, VariableTerm(v2) -> retIfEquals v2 p
                | _ -> fun x -> VariableTerm x

            unifyParametersWithArguments parameters arguments
            |> Option.bind (fun unifiedArgs ->
                let newExpr = 
                    List.zip parameters unifiedArgs
                    |> List.fold (fun acc (p, b) -> unifyExpression acc (changeVariable p b)) expression
                (newExpr, unifiedArgs)
                |> Some)

        unifyExpressionByParams parameters arguments body
        |> Option.bind (fun (resultBody, resultParameters) -> Some(Rule(Signature(name, toParams resultParameters), resultBody)))
    
    let rec unifyListTerms (t1: TypedListTerm) (t2: TypedListTerm): Term -> Term =
        match (t1, t2) with
        | NilTerm, NilTerm -> fun v -> v
        | VarListTerm(v1), s -> fun v -> if v = VariableTerm(v1) then ListTerm(s) else v
        | TypedListTerm(t1, r1), TypedListTerm(t2, r2) ->
            fun v -> if v = t1 then t2 else unifyListTerms r1 r2 v
        | _ -> failwith "???"

    let rec unifyResultToParameters arguments initialExpression expression =
        let unifyWithArgs (args: Term list) (v1: Term) (v2: Term) =
            args
            |> List.map (fun a -> 
                match v1, v2 with
                | _ when a = v1 -> v2
                | ListTerm(l1), ListTerm(l2) -> unifyListTerms l1 l2 a
                | _ -> a
            )

        match (initialExpression, expression) with
        | (True, True) -> arguments
        | (False, False) -> []
        | (Cut, Cut) -> arguments
        | (_, NotExecuted _) -> arguments
        | (NotExpression e1, NotExpression e2) -> unifyResultToParameters arguments e1 e2
        | (OrExpression(e1, e2), OrExpression(e3, e4)) -> unifyResultToParameters (unifyResultToParameters arguments e1 e3) e2 e4
        | (AndExpression(e1, e2), AndExpression(e3, e4)) -> unifyResultToParameters (unifyResultToParameters arguments e1 e3) e2 e4
        | (ResultExpression e1, ResultExpression e2) -> arguments |> List.map (fun a -> if a = e1 then e2 else a)
        | (CallExpression(GoalSignature(name1, goalArgs1)), CallExpression(GoalSignature(name2, goalArgs2))) when name1 = name2 && goalArgs1.Length = goalArgs2.Length ->
            List.fold2 (fun args (arg1) (arg2) -> unifyWithArgs args arg1 arg2) arguments (fromArgs goalArgs1) (fromArgs goalArgs2)
        | (CalcExpr(v1, _), CalcExpr(v2, _)) -> unifyWithArgs arguments v1 v2
        | (EqExpr(v1, v2), EqExpr(v3, v4)) -> unifyWithArgs (unifyWithArgs arguments v1 v3) v2 v4
        | (GrExpr(v1, v2), GrExpr(v3, v4)) -> unifyWithArgs (unifyWithArgs arguments v1 v3) v2 v4
        | (LeExpr(v1, v2), LeExpr(v3, v4)) -> unifyWithArgs (unifyWithArgs arguments v1 v3) v2 v4
        | _ -> failwithf "failed to unify result. %O != %O" initialExpression expression