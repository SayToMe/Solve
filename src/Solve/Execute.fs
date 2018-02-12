namespace Solve

open TermTypes

open Rule
open Rule.Transformers

open VariableUnify
open ExpressionUnify

module Execute =
    let rec executeCalc (calc: Calc) =
        let getInnerNumber =
            function
            | Value (TypedTerm(TypedNumberTerm(x))) -> x
            | _ as inner -> executeCalc inner
        let op1Inner (op: double -> double) (in1: Calc) =
            let (NumberTerm(n1)) = getInnerNumber in1
            NumberTerm(op n1)
        let op2Inner (op: double -> double -> double) (in1: Calc) (in2: Calc) =
            let (NumberTerm(n1)) = getInnerNumber in1
            let (NumberTerm(n2)) = getInnerNumber in2
            NumberTerm(op n1 n2)
        let safeDelete n1 n2 =
            if n2 = 0. then
                nan
            else
                n1 / n2

        match calc with
        | Value (TypedTerm(TypedNumberTerm(NumberTerm v1))) -> NumberTerm v1
        | Value (StructureTerm(Structure(functor', args))) ->
            match functor' with
            | "+" when args.Length = 2 -> executeCalc (Plus(Value(args.[0]), Value(args.[1])))
            | "-" when args.Length = 2 -> executeCalc (Subsctruct(Value(args.[0]), Value(args.[1])))
            | "*" when args.Length = 2 -> executeCalc (Multiply(Value(args.[0]), Value(args.[1])))
            | "/" when args.Length = 2 -> executeCalc (Division(Value(args.[0]), Value(args.[1])))
            | "-" when args.Length = 1 -> executeCalc (Invert(Value(args.[0])))
            | "sqrt" when args.Length = 1 -> executeCalc (Sqrt(Value(args.[0])))
            | "log" when args.Length = 2 -> executeCalc (Log(Value(args.[0]), Value(args.[1])))
            | _ as c -> failwithf "Cant find according calc functor'. %A" c
        | Plus (c1, c2) -> op2Inner (+) c1 c2
        | Subsctruct (c1, c2) -> op2Inner (-) c1 c2
        | Multiply (c1, c2) -> op2Inner (*) c1 c2
        | Division (c1, c2) -> op2Inner safeDelete c1 c2
        | Invert (c1) -> op1Inner (~-) c1
        | Sqrt (c1) -> op1Inner System.Math.Sqrt c1
        | Log (c1, c2) -> op2Inner (fun v n -> System.Math.Log(v, n)) c1 c2
        | _ as c -> failwithf "incorrect calc expression called. %A" c

    // TODO: maybe we should unify each time we execute expression?
    // IDEA IS:
    // rewrite as search for goal(Expression)
    // no execute custom, that should be accessible by knowledgebase right here probably
    // no change variable fn, goal is unified right there
    let rec executeExpression (expr: Expression) (executeCustom: GoalSignature -> #seq<Term list>) (changeVariableFn: Variable -> Term) =
        let keepOnlyFirstCut exprs =
            let rec exprHasCut e =
                match e with
                | Cut -> true
                | AndExpression(e1, e2) -> exprHasCut e1 || exprHasCut e2
                | OrExpression(e1, e2) -> exprHasCut e1 || exprHasCut e2
                | NotExpression(e) -> exprHasCut e
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
            | VariableTerm(v) -> changeVariable v
            | a -> a
            
        // TODO check structure execute is correct
        let rec executeMap (condition: TypedTerm -> TypedTerm -> bool) (e1: Term) (e2: Term): (Term * Term) seq =
            // Hack for equality check
            let conditionIsEquality = condition (TypedNumberTerm(NumberTerm(1.))) (TypedNumberTerm(NumberTerm(1.)))

            let e1 = changeIfVariable changeVariableFn e1
            let e2 = changeIfVariable changeVariableFn e2
            match (e1, e2) with
            | (VariableTerm(_), VariableTerm(_)) -> Seq.singleton (e2, e2)
            | (VariableTerm(_), TypedTerm(_)) -> Seq.singleton (e2, e2)
            | (VariableTerm(_), StructureTerm(_)) -> Seq.singleton (e2, e2)
            | (VariableTerm(_), ListTerm(_)) -> Seq.singleton (e2, e2)
            | (TypedTerm(_), VariableTerm(_)) -> Seq.singleton (e1, e1)
            | (StructureTerm(_), VariableTerm(_)) -> Seq.singleton (e1, e1)
            | (ListTerm(_), VariableTerm(_)) -> Seq.singleton (e1, e1)
            | (TypedTerm(v1), TypedTerm(v2)) ->
                if condition v1 v2 then
                    Seq.singleton (e1, e2)
                else
                    Seq.empty
            | (StructureTerm(s1), StructureTerm(s2)) ->
                if conditionIsEquality && s1 = s2 then
                    Seq.singleton (e1, e2)
                else
                    Seq.empty
            | (ListTerm l1, ListTerm l2) ->
                let rec procList2 l1 l2 =
                    match l1, l2 with
                    | NilTerm, NilTerm -> Seq.singleton (NilTerm, NilTerm)
                    | VarListTerm _, _ -> Seq.singleton (l2, l2)
                    | _, VarListTerm _ -> Seq.singleton (l1, l1)
                    | TypedListTerm(t1, r1), TypedListTerm(t2, r2) ->
                        let t1 = changeIfVariable changeVariableFn t1
                        let t2 = changeIfVariable changeVariableFn t2

                        let unift = executeMap condition t1 t2

                        unift
                        |> Seq.map fst
                        |> Seq.collect (fun t -> 
                            procList2 r1 r2
                            |> Seq.map (fun (p1, p2) -> 
                                (TypedListTerm(t, p1), TypedListTerm(t, p2))
                            )
                        )
                    | _ -> Seq.empty
                procList2 l1 l2
                |> Seq.map (fun (lp1, lp2) -> ListTerm(lp1), ListTerm(lp2))
            | _ -> failwith "unexpected execute binary expression arguments"

        let rec executeBinaryExpression (functor': Term * Term -> Expression) (condition: TypedTerm -> TypedTerm -> bool) (e1: Term) (e2: Term): Expression seq =
            executeMap condition e1 e2 |> Seq.map functor'
        
        match expr with
        | True -> Seq.singleton True
        | False -> Seq.empty
        | Cut -> Seq.singleton Cut
        | NotExpression e ->
            let executed = executeExpression (AndExpression(Cut, e)) executeCustom changeVariableFn
            if Seq.isEmpty executed then
                Seq.singleton (NotExpression e)
            else
                Seq.empty
        | OrExpression (e1, e2) ->
            let first = executeExpression e1 executeCustom changeVariableFn |> Seq.map (fun v -> OrExpression(v, NotExecuted e2))
            let second = (executeExpression e2 executeCustom changeVariableFn |> Seq.map (fun x -> OrExpression(NotExecuted e1, x)))
            
            Seq.append first second |> keepOnlyFirstCut
        | AndExpression (e1, e2) ->
            let executed1 = executeExpression e1 executeCustom changeVariableFn

            match e2 with
            | Cut -> Seq.truncate 1 executed1 |> Seq.map (fun e1res -> AndExpression(e1res, e2))
            | _ ->
                executed1
                |> Seq.collect (fun _e1 ->
                    let fixChangedVariables1 =  getChangedVariableFns e1 _e1

                    fixChangedVariables1
                    |> Seq.collect (fun fn ->
                        let _e2 = unifyExpression e2 fn
                        let fixChangedVariables2 = getChangedVariableFns e2 _e2

                        fixChangedVariables2
                        |> Seq.collect (fun fn ->
                            executeExpression _e2 executeCustom fn
                            |> Seq.map (fun _e2res -> AndExpression(_e1, _e2res))
                        )
                    )
                )
        | ResultExpression e -> Seq.singleton (ResultExpression e)
        | CallExpression (GoalSignature(name, args)) ->
            executeCustom (GoalSignature(name, args))
            |> Seq.map (fun resTerms -> CallExpression(GoalSignature(name, toArgs resTerms)))
        | CalcExpr (v, c) ->
            let v = changeIfVariable changeVariableFn v
            let c = unifyCalc changeVariableFn c
            match v with
            | VariableTerm(_) -> Seq.singleton (CalcExpr(TypedTerm(TypedNumberTerm(executeCalc c)), c))
            | TypedTerm(TypedNumberTerm(v)) when v = (executeCalc c) -> Seq.singleton (CalcExpr(TypedTerm(TypedNumberTerm(v)), c))
            | _ -> Seq.empty
        | EqExpr (e1, e2) -> executeBinaryExpression EqExpr (=) e1 e2
        | GrExpr (e1, e2) -> executeBinaryExpression GrExpr (>) e1 e2
        | LeExpr (e1, e2) -> executeBinaryExpression LeExpr (<) e1 e2
        | _ -> Seq.empty
    
    let getExpressionVariables expr =
        let rec getVariablesFromTerm term =
            match term with
            | VariableTerm(v) -> [v]
            | StructureTerm(Structure(_, terms)) -> terms |> List.collect getVariablesFromTerm
            | ListTerm(l) -> 
                match l with
                | NilTerm -> []
                | VarListTerm(v) -> [v]
                | TypedListTerm(t, l) ->
                    match t with
                    | VariableTerm(v) -> [v] @ getVariablesFromTerm (ListTerm(l))
                    | _ -> getVariablesFromTerm (ListTerm(l))
            | _ -> []

        let rec getExprVariables expr =
            match expr with
            | True -> []
            | False -> []
            | Cut -> []
            | NotExpression e ->
                // ?- getExprVariables e
                []
            | OrExpression (e1, e2) ->
                getExprVariables e1 @ getExprVariables e2
            | AndExpression (e1, e2) ->
                getExprVariables e1 @ getExprVariables e2
            | ResultExpression t -> getVariablesFromTerm t
            | CallExpression (GoalSignature(name, args)) ->
                args |> fromArgs |> List.collect getVariablesFromTerm
            | CalcExpr (v, c) ->
                // ?
                getVariablesFromTerm v
            | EqExpr (e1, e2) -> getVariablesFromTerm e1 @ getVariablesFromTerm e2
            | GrExpr (e1, e2) -> getVariablesFromTerm e1 @ getVariablesFromTerm e2
            | LeExpr (e1, e2) -> getVariablesFromTerm e1 @ getVariablesFromTerm e2
            | _ -> []
        getExprVariables expr
        |> List.distinct
        
    // Assumption: expressions are the same
    let getExpressionVariableValues expr resexpr =
        let rec getVariableValueFromTerm (term: Term) (resterm: Term) =
            match term with
            | VariableTerm(v) -> [(v, resterm)]
            | StructureTerm(Structure(_, terms)) ->
                match resterm with
                | StructureTerm(Structure(_, resterms)) when terms.Length = resterms.Length ->
                    (terms, resterms)
                    ||> List.map2 (fun t1 t2 -> getVariableValueFromTerm t1 t2)
                    |> List.collect (fun x -> x)
                | StructureTerm(Structure(_, resterms)) when terms.Length <> resterms.Length ->
                    failwith "Structure term could be unified only with structure term of same arity"
                | _ -> failwith "Structure term can't be unified with anything by structure term"
            | ListTerm(l) ->
                match resterm with
                | ListTerm(resl) ->
                    match l, resl with
                    | NilTerm, NilTerm -> []
                    | VarListTerm(v), valt -> [(v, ListTerm(valt))]
                    | TypedListTerm(t, tail), TypedListTerm(t1, tail1) ->
                        match t with
                        | VariableTerm(v) -> [(v, t1)] @ getVariableValueFromTerm (ListTerm tail) (ListTerm tail1)
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
            | OrExpression (e1, e2), OrExpression (e1', e2') ->
                getExprVariables e1 e1' @ getExprVariables e2 e2'
            | AndExpression (e1, e2), AndExpression (e1', e2')  ->
                getExprVariables e1 e1' @ getExprVariables e2 e2'
            | ResultExpression t, ResultExpression t' -> getVariableValueFromTerm t t'
            | CallExpression (GoalSignature(name, args)), CallExpression (GoalSignature(name', args')) when name = name' && args.Length = args'.Length ->
                (fromArgs args, fromArgs args') ||> List.map2 (fun a a' -> getVariableValueFromTerm a a') |> List.collect (fun x -> x)
            | CalcExpr (v, _), CalcExpr (v', _) ->
                getVariableValueFromTerm v v'
            | EqExpr (e1, e2), EqExpr (e1', e2') -> getVariableValueFromTerm e1 e1' @ getVariableValueFromTerm e2 e2'
            | GrExpr (e1, e2), GrExpr (e1', e2') -> getVariableValueFromTerm e1 e1' @ getVariableValueFromTerm e2 e2'
            | LeExpr (e1, e2), LeExpr (e1', e2') -> getVariableValueFromTerm e1 e1' @ getVariableValueFromTerm e2 e2'
            | _ -> failwithf "Failed to retrieve variables from %A to %A" expr resexpr
        getExprVariables expr resexpr
        |> List.distinct

    let postExecuteUnify fromArgs resArgs =
        fromArgs
        |> Seq.map (fun vs ->
            let rec procl l1 l2 =
                match l1, l2 with
                | NilTerm, NilTerm -> NilTerm
                | VarListTerm(v1), VarListTerm(_) -> VarListTerm(v1)
                | VarListTerm(_), v2 -> v2
                | v1, VarListTerm(_) -> v1
                | TypedListTerm(t1, r1), TypedListTerm(t2, r2) ->
                    match t1, t2 with
                    | VariableTerm(_), VariableTerm(_) -> TypedListTerm(t2, procl r1 r2)
                    | _ -> TypedListTerm(t2, procl r1 r2)
                | _ -> failwith "?????"

            let res =
                (vs, resArgs)
                ||> List.map2 (fun v arg ->
                    match v, arg with
                    | VariableTerm(_), VariableTerm(_) -> (v, arg)
                    | ListTerm(l1), ListTerm(l2) -> (v, ListTerm(procl l1 l2))
                    | _ -> (v, v)
                )
                        
            (vs)
            |> List.map (fun (v) -> 
                let (_, vr) = List.find (fun (vv, _) -> vv = v) res
                vr
            )
        )

    //let f() =
    //    postExecuteUnify (unifyResultToParameters (fromParams unifiedRuleParameters) expr) results goalArguments

    // Idea is:
    // Expression is unified with arguments by parameters
    // Expression executes and all variables are resolved
    // Expression tree should be mostly unchanged
    // All changed variables can be caught afterwards
    let executeCustomExpression (Goal(expr)) (executeCustom: GoalSignature -> #seq<Term list>): ((Variable * Term) list) seq =
        executeExpression expr executeCustom (fun v -> VariableTerm(v))
        |> Seq.map (fun resExpr -> getExpressionVariableValues expr resExpr)

        //let arguments = toArgs goalArguments

        //match unifyRule rule arguments with
        //| Some (Rule(Signature(ruleName, unifiedRuleParameters), expr)) -> 
        //    if name = ruleName then
        //        let changeVar = 
        //            (unifiedRuleParameters, arguments)
        //            ||> List.fold2 (fun acc (Parameter(p)) (Argument(a)) -> fun v -> if VariableTerm(v) = p then a else acc v) (fun v -> VariableTerm(v))

        //        let results = executeExpression expr executeCustom changeVar
        //        let postResults = postExecuteUnify (unifyResultToParameters (fromParams unifiedRuleParameters) expr) results goalArguments
        //        postResults
        //    else
        //        Seq.empty
        //| None -> Seq.empty

    let exExpr (expr: Expression) (executeCustom: GoalSignature -> #seq<Term list>) (changeVariableFn: Variable -> Term): ((Variable * Term) list) seq =
        executeExpression expr executeCustom changeVariableFn
        |> Seq.map (fun resExpr -> getExpressionVariableValues expr resExpr)