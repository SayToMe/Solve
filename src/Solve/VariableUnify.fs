namespace Solve

open TermTypes

open Rule

module VariableUnify =
    let private changeIfVariable (changeVariable: Variable -> Term) =
        function
        | VariableTerm(variable) -> changeVariable variable
        | term -> term
        
    let changeVariablesForStruct (changeVariable: Variable -> Term) (Structure(functor', prms)) =
        Structure(functor', prms |> List.map (changeIfVariable changeVariable))

    let rec changeVariablesForList (changeVariable: Variable -> Term) (list: TypedListTerm) =
        match list with
        | NilTerm -> NilTerm
        | VarListTerm varListTerm -> 
            match changeVariable varListTerm with
            | VariableTerm(variable) -> VarListTerm variable
            | term -> TypedListTerm(term, NilTerm)
        | TypedListTerm(t1, r1) -> TypedListTerm(changeIfVariable changeVariable t1, changeVariablesForList changeVariable r1)
    
    let rec unifyParametersWithArguments (parameters: Parameter list) (arguments: Argument list) =
        let rec unifyRightToConcreteLeft (leftTerm: Term) (rightTerm: Term) =
            match (leftTerm, rightTerm) with
            | (_, VariableTerm(_)) -> Some leftTerm
            | (VariableTerm(_), _) -> Some rightTerm
            | (TypedTerm(leftTypedTerm), TypedTerm(rightTypedTerm)) when leftTypedTerm = rightTypedTerm -> Some rightTerm
            | (StructureTerm(Structure(leftFunctor, leftParameters)), StructureTerm(Structure(rightFunctor, rightParameters))) when leftFunctor = rightFunctor && leftParameters.Length = rightParameters.Length ->
                let newArgs = List.map2 (fun leftVariable rightVariable -> unifyRightToConcreteLeft leftVariable rightVariable) leftParameters rightParameters
                if List.exists Option.isNone newArgs then
                    None
                else
                    let newArgs = newArgs |> List.map Option.get
                    Some(StructureTerm(Structure(leftFunctor, newArgs)))
            | (ListTerm(leftListTerm), ListTerm(rightListTerm)) ->
                match (leftListTerm, rightListTerm) with
                | NilTerm, NilTerm -> Some leftTerm
                | _, VarListTerm _ -> Some leftTerm
                | VarListTerm _, _ -> Some rightTerm
                | TypedListTerm(leftTerm, leftTail), TypedListTerm(rightTerm, rightTail) -> 
                    unifyRightToConcreteLeft leftTerm rightTerm
                    |> Option.bind (fun unifiedTerm ->
                        let concatListTerm =
                            function
                            | ListTerm(r) -> Some(ListTerm(TypedListTerm(unifiedTerm, r)))
                            | _ -> failwith "List term"
                        unifyRightToConcreteLeft (ListTerm leftTail) (ListTerm rightTail) |> Option.bind concatListTerm)
                | _ -> None
            | _ -> None
        
        if parameters.Length = arguments.Length then
            let prms = List.map2 (fun (Parameter(paramer)) (Argument(argument)) -> unifyRightToConcreteLeft paramer argument) parameters arguments
            if List.exists Option.isNone prms then
                None
            else
                Some <| List.map Option.get prms
         else
             None