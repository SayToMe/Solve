namespace Solve

open TermTypes

open Rule

module VariableUnify =
    let processStruct changeVariable (Structure(functor', prms)) =
        let changeIfVariable =
            function
            | VariableTerm(v) -> changeVariable v
            | a -> a
        Structure(functor', prms |> List.map changeIfVariable)

    let rec unifyTwoAny v1 v2 =
        match (v1, v2) with
        | (VariableTerm(_), VariableTerm(_)) -> Some v1
        | (VariableTerm(_), TypedTerm(_)) -> Some v2
        | (VariableTerm(_), StructureTerm(_)) -> Some v2
        | (TypedTerm(_), VariableTerm(_)) -> Some v1
        | (StructureTerm(_), VariableTerm(_)) -> Some v1
        | (TypedTerm(vt1), TypedTerm(vt2)) when vt1 = vt2 -> Some v2
        | (StructureTerm(Structure(f1, p1)), StructureTerm(Structure(f2, p2))) when f1 = f2 && p1.Length = p2.Length ->
            let newArgs = List.map2 (fun v1 v2 -> unifyTwoAny v1 v2) p1 p2
            if List.exists Option.isNone newArgs then
                None
            else
                let newArgs = newArgs |> List.map Option.get
                Some(StructureTerm(Structure(f1, newArgs)))
        | _ -> None
        
    let postUnifyUnaryExpressions v1 v2 fn v =
        if VariableTerm(v) = v1 then 
            v2 
        else 
            fn v

    let postUnifyBinaryExpression proc functor' e1 e2 =
        match (e1, e2) with
        | (VariableTerm(v1), VariableTerm(v2)) -> functor'(proc v1, proc v2)
        | (VariableTerm(v1), TypedTerm(_)) -> functor'(proc v1, e2)
        | (VariableTerm(v1), StructureTerm(v2)) -> functor'(proc v1, StructureTerm(processStruct proc v2))
        | (TypedTerm(_), VariableTerm(v2)) -> functor'(e1, proc v2)
        | (StructureTerm(v1), VariableTerm(v2)) -> functor'(StructureTerm(processStruct proc v1), proc v2)
        | _ -> functor'(e1, e2)

    let postUnifyBinaryExpressions (v1, v2) (v3, v4) fn v =
        if VariableTerm(v) = v1 then
            v3 
        else if VariableTerm(v) = v2 then 
            v4 
        else fn v
        
    let rec unifyParamsWithArguments parameters arguments =
        let prms = List.map2 (fun (Parameter(p)) (Argument(a)) -> unifyTwoAny p a) parameters arguments
        if List.exists Option.isNone prms then
            None
        else
            Some <| List.map Option.get prms