namespace Solve

open TermTypes

open Rule

module VariableUnify =
    let private changeIfVariable (changeVariable: Variable -> Term) =
        function
        | VariableTerm(v) -> changeVariable v
        | term -> term
        
    let processStruct (changeVariable: Variable -> Term) (Structure(functor', prms)) =
        Structure(functor', prms |> List.map (changeIfVariable changeVariable))

    let rec processList (changeVariable: Variable -> Term) (list: TypedListTerm) =
        match list with
        | NilTerm -> NilTerm
        | VarListTerm v -> 
            match changeVariable v with
            | VariableTerm(v) -> VarListTerm(v)
            | term -> TypedListTerm(term, NilTerm)
        | TypedListTerm(t1, r1) -> TypedListTerm(changeIfVariable changeVariable t1, processList changeVariable r1)

    let rec unifyConcreteRightToLeft (t1: Term) (t2: Term) =
        match (t1, t2) with
        | (VariableTerm(_), VariableTerm(_)) -> Some t2
        | (VariableTerm(_), _) -> Some t2
        | (_, VariableTerm(_)) -> Some t1
        | (TypedTerm(vt1), TypedTerm(vt2)) when vt1 = vt2 -> Some t2
        | (StructureTerm(Structure(f1, p1)), StructureTerm(Structure(f2, p2))) when f1 = f2 && p1.Length = p2.Length ->
            let newArgs = List.map2 (fun v1 v2 -> unifyConcreteRightToLeft v1 v2) p1 p2
            if List.exists Option.isNone newArgs then
                None
            else
                let newArgs = newArgs |> List.map Option.get
                Some(StructureTerm(Structure(f1, newArgs)))
        | (ListTerm(l1), ListTerm(l2)) ->
            match (l1, l2) with
            | VarListTerm _, VarListTerm _ -> Some (t2)
            | VarListTerm _, _ -> Some (t2)
            | _, VarListTerm _ -> Some (t1)
            | NilTerm, NilTerm -> Some t1
            | TypedListTerm(l1, r1), TypedListTerm(l2, r2) -> 
                unifyConcreteRightToLeft l1 l2 |> Option.bind (fun l -> unifyConcreteRightToLeft (ListTerm r1) (ListTerm r2) |> Option.bind (fun (ListTerm(r)) -> Some <| ListTerm(TypedListTerm(l, r))))
            | _ -> None
        | _ -> None
        
    let backwardsTermUnification (t1: Term) (t2: Term) (fn: Variable -> Term) (v: Variable) =
        if VariableTerm(v) = t1 then 
            t2 
        else 
            fn v

    // TODO: check if there should be inner structure unification
    let postUnifyBinaryExpression (proc: Variable -> Term) (functor': Term * Term -> 'a) (t1: Term) (t2: Term) =
        match (t1, t2) with
        | (VariableTerm(v1), VariableTerm(v2)) -> functor'(proc v1, proc v2)
        | (VariableTerm(v1), TypedTerm(_)) -> functor'(proc v1, t2)
        | (VariableTerm(v1), StructureTerm(v2)) -> functor'(proc v1, StructureTerm(processStruct proc v2))
        | (TypedTerm(_), VariableTerm(v2)) -> functor'(t1, proc v2)
        | (StructureTerm(v1), VariableTerm(v2)) -> functor'(StructureTerm(processStruct proc v1), proc v2)
        | (ListTerm(l1), ListTerm(l2)) -> functor'(ListTerm(processList proc l1), ListTerm(processList proc l2))
        | _ -> functor'(t1, t2)

    let postUnifyBinaryExpressions ((t1, t2): Term * Term) ((t3, t4): Term * Term) (fn: Variable -> Term) (v: Variable) =
        if VariableTerm(v) = t1 then
            t3 
        else if VariableTerm(v) = t2 then 
            t4 
        else fn v
        
    let rec unifyParamsWithArguments (parameters: Parameter list) (arguments: Argument list) =
        let prms = List.map2 (fun (Parameter(p)) (Argument(a)) -> unifyConcreteRightToLeft p a) parameters arguments
        if List.exists Option.isNone prms then
            None
        else
            Some <| List.map Option.get prms