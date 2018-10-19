namespace Solve

open TermTypes

open Rule

module VariableUnify =
    let inline bindOptionalList (list: list<Option<_>>) =
        if List.exists Option.isNone list then
            None
        else
            Some <| List.map Option.get list

    open Rule

    let rec private changeVariablesRecursive (changeVariable: Variable -> Term) =
        function 
        | VariableTerm(variable) -> changeVariable variable
        | StructureTerm(Structure(functor', prms)) ->
            let newPrms = prms |> List.map (changeVariablesRecursive changeVariable)
            StructureTerm(Structure(functor', newPrms))
        | ListTerm(list) ->
            match list with
            | NilTerm -> ListTerm(NilTerm)
            | VarListTerm v ->
                match changeVariable v with 
                | VariableTerm vt -> ListTerm(VarListTerm(vt))
                | vt -> ListTerm(TypedListTerm(vt, NilTerm))
            | TypedListTerm(head, tail) ->
                match changeVariablesRecursive changeVariable (ListTerm(tail)) with 
                | ListTerm(changedTail) -> ListTerm(TypedListTerm(changeVariablesRecursive changeVariable head, changedTail))
                | _ -> failwith ""
        | t -> t
        
    let changeVariablesForStruct (changeVariable: Variable -> Term) (structure: Structure) =
        match changeVariablesRecursive changeVariable (StructureTerm(structure)) with 
        | StructureTerm(s) -> s
        | _ -> failwith ""

    let rec changeVariablesForList (changeVariable: Variable -> Term) (list: TypedListTerm) =
        match changeVariablesRecursive changeVariable (ListTerm(list)) with 
        | ListTerm(l) -> l
        | _ -> failwith ""

    type Source = Source of Term
    type Dest = Dest of Term
    type Unified = Unified of Term

    /// 
    /// 
    /// 
    /// 
    /// 
    /// 
    /// 
    /// 

    /// Source -> Dest
    /// 1 -> 1 => 1
    /// X -> 1 => 1
    /// 1 -> X => 1
    /// X -> Y => Y // or should be X -> Y => X (!)
    /// (1, X, 3, 4) => (A, B, C | R) => (1, B, 3, 4) / (1, X, 3, 4)
    /// Why should variable name change
    /// - In case we have call like (X, X) -> (A, B) => A should become B
    /// Why should variable name persist
    /// - In case we have bounded variable that should be renamed for whole nested expression with possible overlaps
    let rec unifyTerms (Source(sourceTerm)) (Dest(destTerm)) =
        let unifyVariables source dest =
            dest

        match (sourceTerm, destTerm) with
            | (VariableTerm(_), VariableTerm(_)) -> Some << Unified <| unifyVariables sourceTerm destTerm
            | (VariableTerm(_), _) -> Some <| Unified destTerm
            | (_, VariableTerm(_)) -> Some <| Unified sourceTerm
            | (TypedTerm(sourceTypedTerm), TypedTerm(destTypedTerm))
                when sourceTypedTerm = destTypedTerm -> Some <| Unified destTerm
            | (StructureTerm(Structure(sourceFunctor, sourceParameters)), StructureTerm(Structure(destFunctor, destParameters)))
                when sourceFunctor = destFunctor && sourceParameters.Length = destParameters.Length ->
                    let sourceParameters = List.map Source sourceParameters
                    let destParameters = List.map Dest destParameters
                    let newArgs = List.map2 unifyTerms sourceParameters destParameters
                    newArgs
                    |> List.map (Option.map (fun (Unified(u)) -> u))
                    |> bindOptionalList
                    |> Option.map (fun newArgs -> Unified <| StructureTerm(Structure(sourceFunctor, newArgs)))
            | (ListTerm(sourceListTerm), ListTerm(destListTerm)) ->
                match (sourceListTerm, destListTerm) with
                | NilTerm, NilTerm -> Some <| Unified sourceTerm
                | _, VarListTerm _ -> Some <| Unified sourceTerm
                | VarListTerm _, _ -> Some <| Unified destTerm
                | TypedListTerm(sourceTerm, sourceTail), TypedListTerm(destTerm, destTail) -> 
                    unifyTerms (Source(sourceTerm)) (Dest(destTerm))
                    |> Option.bind (fun (Unified(unifiedTerm)) ->
                        let concatListTerm = function | (Unified(ListTerm(r))) -> Unified <| ListTerm(TypedListTerm(unifiedTerm, r)) | _ -> failwith ""
                        unifyTerms (Source(ListTerm sourceTail)) (Dest(ListTerm destTail))
                        |> Option.map concatListTerm
                    )
                | _ -> None
            | _ -> None

    let rec private _unifyFromDestSourceUnification (Dest(destTerm)) (Unified(unifiedDestTerm)) (term: Term) =
        // Dest term can not be unified with another variable name (?)
        // Gather all variable changes from sourceTerm by unification
        // Try to apply to dest term
        match destTerm, unifiedDestTerm with 
        | VariableTerm(v), VariableTerm(v2) ->
            if v <> v2 then
                // failwith "Unexpected variable name for unified dest term"
//                let (Variable(v), Variable(v2)) = v, v2
//                Some (VariableTerm (Variable (v + "_" + v2)))
                Some unifiedDestTerm
            else
                Some term
        | VariableTerm(v), _ -> changeVariablesRecursive (fun vv -> if vv = v then unifiedDestTerm else VariableTerm(vv)) term |> Some
        | StructureTerm(Structure(_, destParameters)), StructureTerm(Structure(_, unifiedDestParameters)) ->
            (destParameters, unifiedDestParameters)
            ||> List.fold2 (fun t c1 c2 -> Option.bind (_unifyFromDestSourceUnification (Dest c1) (Unified c2)) t) (Some term)
        | ListTerm(destList), ListTerm(unifiedDestList) ->
            match destList, unifiedDestList with
            | NilTerm, NilTerm -> Some term
            | VarListTerm(v), NilTerm
            | VarListTerm(v), TypedListTerm(_, _) ->
                changeVariablesRecursive (fun vv -> if vv = v then ListTerm(unifiedDestList) else VariableTerm(vv)) term
                |> Some
            | VarListTerm(v), VarListTerm(v2) ->
                if v <> v2 then failwith "Unexpected variable name for unified dest term" else Some term
            | TypedListTerm(destHead, destTail), TypedListTerm(unifiedDestHead, unifiedDestTail) ->
                _unifyFromDestSourceUnification (Dest(destHead)) (Unified(unifiedDestHead)) term
                |> Option.bind (_unifyFromDestSourceUnification (Dest(ListTerm(destTail))) (Unified(ListTerm(unifiedDestTail))))
            | _ -> Some term
        | _ -> Some term

    let rec private _unifyDestsFromSources (sources: Source list) (dests: Dest list) =
        let unifies = List.map2 unifyTerms sources dests
        
        bindOptionalList unifies
        |> Option.map (List.zip3 sources dests)
        |> Option.bind (fun unifies ->
            (sources, dests, unifies)
            |||> List.map3 (fun s d (_, _, u) ->
                (Some u, unifies)
                ||> List.fold (fun unificationResult (su, du, uu) ->
                    let (Dest(d)) = d
                    let one = _unifyFromDestSourceUnification du uu d
                    let (Source(s)) = s
                    let one2 = _unifyFromDestSourceUnification du uu s
                    let two =  unificationResult |> Option.bind (fun (Unified(t)) -> _unifyFromDestSourceUnification du uu t)
                    one
                    |> Option.bind (fun o -> two |> Option.bind (fun t -> unifyTerms (Source(o)) (Dest(t))))
                )
            )
            |> bindOptionalList
        )

    let unifyParamsWithArgs (parameters: Parameter list) (arguments: Argument list) =
        _unifyDestsFromSources (Transformers.fromArgs arguments |> List.map Source) (Transformers.fromParams parameters |> List.map Dest)

    /// Unifies second term to the first one if it was concrete
//    let rec private _unifyRightToConcreteLeft (leftTerm: Term) (rightTerm: Term) =
//        match (leftTerm, rightTerm) with
//        | (_, VariableTerm(_)) -> Some leftTerm // TODO: check if it's OK
//        | (VariableTerm(_), _) -> Some rightTerm
//        | (TypedTerm(leftTypedTerm), TypedTerm(rightTypedTerm)) when leftTypedTerm = rightTypedTerm -> Some rightTerm
//        | (StructureTerm(Structure(leftFunctor, leftParameters)), StructureTerm(Structure(rightFunctor, rightParameters)))
//            when leftFunctor = rightFunctor && leftParameters.Length = rightParameters.Length ->
//                let newArgs = List.map2 (fun leftVariable rightVariable -> _unifyRightToConcreteLeft leftVariable rightVariable) leftParameters rightParameters
//                if List.exists Option.isNone newArgs then
//                    None
//                else
//                    let newArgs = newArgs |> List.map Option.get
//                    Some(StructureTerm(Structure(leftFunctor, newArgs)))
//        | (ListTerm(leftListTerm), ListTerm(rightListTerm)) ->
//            match (leftListTerm, rightListTerm) with
//            | NilTerm, NilTerm -> Some leftTerm
//            | _, VarListTerm _ -> Some leftTerm
//            | VarListTerm _, _ -> Some rightTerm
//            | TypedListTerm(leftTerm, leftTail), TypedListTerm(rightTerm, rightTail) -> 
//                _unifyRightToConcreteLeft leftTerm rightTerm
//                |> Option.bind (fun unifiedTerm ->
//                    let concatListTerm =
//                        function
//                        | ListTerm(r) -> Some(ListTerm(TypedListTerm(unifiedTerm, r)))
//                        | _ -> failwith "List term"
//                    _unifyRightToConcreteLeft (ListTerm leftTail) (ListTerm rightTail) |> Option.bind concatListTerm)
//            | _ -> None
//        | _ -> None
//
//    let rec private unifyParametersWithArgumentsOnlyPositional (parameters: Parameter list) (arguments: Argument list) =
//        if parameters.Length = arguments.Length then
//            let prms = List.map2 (fun (Parameter(paramer)) (Argument(argument)) -> _unifyRightToConcreteLeft paramer argument) parameters arguments
//            bindOptionalList prms
//        else
//            None
//
//    let rec private unifyParametersAfterPositional (parameters: Parameter list) (postUnifyParameters: Parameter list) =
//        let rawChanges = 
//            List.zip (Rule.Transformers.fromParams parameters) (Rule.Transformers.fromParams postUnifyParameters)
//            |> List.fold (fun changes (initial, concrete) ->
//                match initial with
//                | VariableTerm(Variable v) when (not <| Helpers.isVariable concrete) ->
//                    (initial, concrete)::changes
//                | _ -> changes
//            ) []
//            
//        rawChanges

    // Probably there is a better design
    // To have two different implementation of unitifactions
    // Based on two cases:
    // Position-based
    // Variable-based
    //
    // So at first glance
    // Position based
    // Goal unifies with Goal if
    // parameters can be unified with arguments
    // 
    // Variable-based
    // All expression variables are unified with all others based on some rules
    // Like taken from position
    //
    // So searching for goal will execute in next steps
    // goal(parameters) -> goal(arguments)
    // parameters -> arguments
    // parameter -> argument on i'th position
    // arguments that had some links to the other positions should be unified after
    //
    // So
    // 1. Unify positionaly
    // 2. Unify by positionaly resolved variables

    let rec unifyParametersWithArguments (parameters: Parameter list) (arguments: Argument list) =
        // unifyParametersWithArgumentsOnlyPositional parameters arguments
        unifyParamsWithArgs parameters arguments
        |> Option.map (List.map (fun (Unified(u)) -> u))