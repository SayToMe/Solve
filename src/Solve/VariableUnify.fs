namespace Solve

open TermTypes

open Rule

module VariableUnify =
    let private changeIfVariable (changeVariable: Variable -> Term) =
        function
        | VariableTerm(v) -> changeVariable v
        | term -> term
        
    let changeVariablesForStruct (changeVariable: Variable -> Term) (Structure(functor', prms)) =
        Structure(functor', prms |> List.map (changeIfVariable changeVariable))

    let rec changeVariablesForList (changeVariable: Variable -> Term) (list: TypedListTerm) =
        match list with
        | NilTerm -> NilTerm
        | VarListTerm v -> 
            match changeVariable v with
            | VariableTerm(v) -> VarListTerm(v)
            | term -> TypedListTerm(term, NilTerm)
        | TypedListTerm(t1, r1) -> TypedListTerm(changeIfVariable changeVariable t1, changeVariablesForList changeVariable r1)
    
    let rec unifyParametersWithArguments (parameters: Parameter list) (arguments: Argument list) =
        let rec unifyRightToConcreteLeft (t1: Term) (t2: Term) =
            match (t1, t2) with
            | (_, VariableTerm(_)) -> Some t1
            | (VariableTerm(_), _) -> Some t2
            | (TypedTerm(vt1), TypedTerm(vt2)) when vt1 = vt2 -> Some t2
            | (StructureTerm(Structure(f1, p1)), StructureTerm(Structure(f2, p2))) when f1 = f2 && p1.Length = p2.Length ->
                let newArgs = List.map2 (fun v1 v2 -> unifyRightToConcreteLeft v1 v2) p1 p2
                if List.exists Option.isNone newArgs then
                    None
                else
                    let newArgs = newArgs |> List.map Option.get
                    Some(StructureTerm(Structure(f1, newArgs)))
            | (ListTerm(l1), ListTerm(l2)) ->
                match (l1, l2) with
                | NilTerm, NilTerm -> Some t1
                | _, VarListTerm _ -> Some (t1)
                | VarListTerm _, _ -> Some (t2)
                | TypedListTerm(l1, r1), TypedListTerm(l2, r2) -> 
                    unifyRightToConcreteLeft l1 l2 |> Option.bind (fun l -> unifyRightToConcreteLeft (ListTerm r1) (ListTerm r2) |> Option.bind (fun (ListTerm(r)) -> Some <| ListTerm(TypedListTerm(l, r))))
                | _ -> None
            | _ -> None
        
        let prms = List.map2 (fun (Parameter(p)) (Argument(a)) -> unifyRightToConcreteLeft p a) parameters arguments
        if List.exists Option.isNone prms then
            None
        else
            Some <| List.map Option.get prms