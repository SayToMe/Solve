namespace Solve

open TermTypes
open Rule

module VariableUnify =
    let inline bindOptionalList (list: list<Option<_>>) =
        if List.exists Option.isNone list then
            None
        else
            Some <| List.map Option.get list

    let rec changeVariablesRecursive (changeVariable: Variable -> Term) =
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

    /// There is a matching between t1 and t2 terms.
    /// After execution there could be changed variables that should be catched by every existing variable
    let backwardsTermUnification (leftTerm: Term) (rightTerm: Term) (procVarOtherChange: Variable -> Term) (variable: Variable) =
        match leftTerm with
        | VariableTerm(variableTerm) when variableTerm = variable -> rightTerm
        | _ -> procVarOtherChange variable

    let rec unifyListTerms (leftListTerm: TypedListTerm) (rightListTerm: TypedListTerm): Term -> Term =
        match (leftListTerm, rightListTerm) with
        | NilTerm, NilTerm -> id
        | VarListTerm(varListTerm), rightListTerm -> fun v -> if v = VariableTerm(varListTerm) then ListTerm(rightListTerm) else v
        | TypedListTerm(leftTerm, leftTail), TypedListTerm(rightTerm, rightTail) ->
            fun variableTerm -> if variableTerm = leftTerm then rightTerm else unifyListTerms leftTail rightTail variableTerm
        | _ -> failwithf "Failed to unify two list terms %A, %A" leftListTerm rightListTerm

    type Source = Source of Term
    type Dest = Dest of Term
    type Unified = Unified of Term

    let fromUnified (Unified(t)) = t

    type UnificationContext(sourceMap: Map<Variable, Term>, destMap: Map<Variable, Term>, preventMapSourceVariables: Variable list) =
        static member Empty = UnificationContext(Map.empty, Map.empty, [])
        member self.AddSource v t =
            if sourceMap.ContainsKey v then
                if sourceMap.Item v <> t then
                    if Helpers.isVariable <| sourceMap.Item v then 
                        Some self
                    else
                        None
                else
                    Some self
            else
                if List.contains v preventMapSourceVariables then 
                    Some self
                else
                    match t with
                    | VariableTerm(variableTerm) ->
                        Some <| UnificationContext(sourceMap.Add (v, t), destMap, variableTerm::preventMapSourceVariables)
                    | _ ->
                        Some <| UnificationContext(sourceMap.Add (v, t), destMap, preventMapSourceVariables)
        member self.AddDest v t =
            if destMap.ContainsKey v then
                if destMap.Item v <> t then
                    if Helpers.isVariable <| destMap.Item v then
                        Some self
                    else
                        None
                else
                    Some self
            else
                Some <| UnificationContext(sourceMap, destMap.Add (v, t), preventMapSourceVariables)
        member self.ApplySource term =
            changeVariablesRecursive (fun v ->
                let preventMap = List.contains v preventMapSourceVariables
            
                if preventMap then 
                    VariableTerm(v)
                else
                    let f = sourceMap.TryFind v
    
                    let r = f |> Option.defaultValue (VariableTerm(v))
                    r
            ) term
        member self.ApplyDest term =
            changeVariablesRecursive (fun v ->
                let f = destMap.TryFind v

                let r = f |> Option.defaultValue (VariableTerm(v))
                r
            ) term
        member self.Process t =
            changeVariablesRecursive (fun v ->
                sourceMap.TryFind v
                // Would it cause StackOverflow for variables into variables?
                |> Option.map (self.Process)
                |> Option.defaultValue (VariableTerm(v))
            ) t
        member self.IsSourceVariableFromDest v =
            preventMapSourceVariables
            |> List.contains v
        override self.ToString() =
            sprintf "SourceMap: %A. DestMap: %A. Prevent: %A." sourceMap destMap preventMapSourceVariables

    type UnificationResult = UnificationResult of term: Unified * context: UnificationContext

    type RecursiveBypassOrder = Down | Up

    /// Idea is pretty simple
    /// Source -> Dest
    /// 1 -> 1 => 1
    /// X -> 1 => 1
    /// 1 -> X => 1
    /// X -> Y => Y
    /// X -> Y => Y & X -> Z => Y
    /// (1, X, 3, 4) => (A, B, C | R) => (1, B, 3, 4)
    let rec _unifyTerms (Source(sourceTerm)) (Dest(destTerm)) (context: UnificationContext) (bypassOrder: RecursiveBypassOrder): UnificationResult option =
        let unifyStructures (Structure(sourceFunctor, sourceParameters)) (Structure(destFunctor, destParameters)) (context: UnificationContext): UnificationResult option =
            let functor' = sourceFunctor
            let sourceParameters = List.map Source sourceParameters
            let destParameters = List.map Dest destParameters
            
            (sourceParameters, destParameters)
            ||> List.fold2 (fun state sourceTerm destTerm ->
                state
                |> Option.bind (fun (res, context) ->
                    _unifyTerms sourceTerm destTerm context bypassOrder
                    |> Option.map (fun (UnificationResult(ut, newContext)) ->
                        (res@[ut], newContext)
                    )
                )
            ) (Some ([], context))
            |> Option.map (fun (t, c) -> UnificationResult(Unified(StructureTerm(Structure(functor', List.map fromUnified t))), c))

        let unifyLists sourceListTerm destListTerm (context: UnificationContext) (bypassOrder: RecursiveBypassOrder): UnificationResult option =
            match (sourceListTerm, destListTerm) with
            | NilTerm, NilTerm -> 
                UnificationResult (Unified (ListTerm NilTerm), context)
                |> Some
            | _, VarListTerm v ->
                context.AddSource v (ListTerm(sourceListTerm))
                |> Option.map (fun c -> UnificationResult (Unified (ListTerm sourceListTerm), c))
            | VarListTerm v, _ ->
                context.AddDest v (ListTerm(destListTerm))
                |> Option.map (fun c -> UnificationResult(Unified (ListTerm destListTerm), c))
            | TypedListTerm(sourceTerm, sourceTail), TypedListTerm(destTerm, destTail) ->
                match bypassOrder with 
                | Down ->
                    let unificationResult = _unifyTerms (Source(sourceTerm)) (Dest(destTerm)) context bypassOrder
                    
                    unificationResult
                    |> Option.bind (fun (UnificationResult (Unified(unifiedTerm), newContext)) ->
                        let concatListTerm =
                            function
                            | UnificationResult(Unified(ListTerm(r)), c) ->
                                UnificationResult(Unified <| ListTerm(TypedListTerm(unifiedTerm, r)), c)
                            | _ -> failwith ""
                            
                        _unifyTerms (Source(ListTerm sourceTail)) (Dest(ListTerm destTail)) newContext bypassOrder
                        |> Option.map concatListTerm
                    )
                | Up ->
                    _unifyTerms (Source(ListTerm sourceTail)) (Dest(ListTerm destTail)) context bypassOrder
                    |> Option.bind (fun (UnificationResult (Unified(unifiedTail), newContext)) ->
                        match unifiedTail with
                        | ListTerm(unifiedTail) ->
                            let unificationResult = _unifyTerms (Source(sourceTerm)) (Dest(destTerm)) newContext bypassOrder
                            unificationResult
                            |> Option.map (fun (UnificationResult(Unified(unifiedTerm), nContext)) ->
                                UnificationResult(Unified <| ListTerm(TypedListTerm(unifiedTerm, unifiedTail)), nContext)
                            )
                        | _ -> failwith ""
                    )
            | _ -> None

        let destTerm = context.ApplyDest destTerm
        let prevSource = sourceTerm
        let sourceTerm = context.ApplySource sourceTerm

        printfn "(%A -> %A) -> %A" prevSource sourceTerm destTerm
        printfn "Context: %A" context
        match (sourceTerm, destTerm) with
            | (VariableTerm(v), VariableTerm(dv)) ->
                if context.IsSourceVariableFromDest v then
                    let unifiedVariable = VariableTerm(v)
                    context.AddDest dv unifiedVariable
                    |> Option.map (fun newContext -> UnificationResult(Unified unifiedVariable, newContext))
                else
                    let unifyVariables source dest =
                        dest
                    let unifiedVariable = unifyVariables sourceTerm destTerm
                    context.AddSource v (unifiedVariable)
                    |> Option.map (fun newContext -> UnificationResult(Unified unifiedVariable, newContext))
            | (VariableTerm(v), _) ->
                context.AddSource v destTerm
                |> Option.map (fun newContext -> UnificationResult(Unified destTerm, newContext))
            | (_, VariableTerm(v)) ->
                context.AddDest v sourceTerm
                |> Option.map (fun newContext -> UnificationResult(Unified sourceTerm, newContext))
            | (TypedTerm(sourceTypedTerm), TypedTerm(destTypedTerm))
                when sourceTypedTerm = destTypedTerm ->
                    UnificationResult(Unified destTerm, context)
                    |> Some
            | (StructureTerm(Structure(sourceFunctor, sourceParameters) as sourceStructure), StructureTerm(Structure(destFunctor, destParameters) as destStructure))
                when sourceFunctor = destFunctor && sourceParameters.Length = destParameters.Length ->
                    unifyStructures sourceStructure destStructure context
            | (ListTerm(sourceListTerm), ListTerm(destListTerm)) ->
                unifyLists sourceListTerm destListTerm context bypassOrder
            | _ -> None

    let unifyTerms (Source(sourceTerm) as source) (Dest(destTerm) as dest) =
        let _unify (Source(sourceTerm) as source) (Dest(destTerm) as dest) bypassOrder =
            _unifyTerms source dest UnificationContext.Empty bypassOrder
            |> Option.map (fun (UnificationResult(r, _)) -> r)
        printfn "Unification: %A -> %A Down" source dest
        let r1 = _unify source dest Down
        printfn "Unification: %A -> %A Up" source dest
        let r2 = _unify source dest Up
        
        (r2, r1)
        |> function
        | (Some(Unified(r1)), Some(Unified(r2))) ->
            printfn "Post Unification: %A -> %A Down" r1 r2
            _unify (Source r1) (Dest r2) Down
        | _ -> None

    let rec private _unifyDestsFromSources (sources: Source list) (dests: Dest list) =
        let sourceTerms = sources |> List.map (fun (Source(t)) -> t)
        let destTerms = dests |> List.map (fun (Dest(t)) -> t)
        unifyTerms (Source(Transformers.anyList sourceTerms)) (Dest(Transformers.anyList destTerms))
        |> Option.map (fun o ->
            match o with
            | (Unified(ListTerm(typedList))) -> typedList |> Transformers.anyListToConcreteTerms |> List.map Unified
            | _ -> failwith ""
        )
        
    // Requires unique variable names for parameters and arguments
    let unifyParamsWithArgs (parameters: Parameter list) (arguments: Argument list): option<Unified list> =
        _unifyDestsFromSources (Transformers.fromArgs arguments |> List.map Source) (Transformers.fromParams parameters |> List.map Dest)

    let nextVarIdGetter =
        let mutable id = 0
        let mutable varId = Map.empty
        let inner(var, key) =
            let innerKey = var + "_" + key
            let varName =
                varId
                |> Map.tryFind innerKey
                |> Option.defaultWith (fun () -> 
                    id <- id + 1
                    id.ToString()
                )
            varId <- varId |> Map.add innerKey varName
            varName
        inner
            
    let rec unifyParametersWithArguments (parameters: Parameter list) (arguments: Argument list) =
        let mutable initialVariableNameMap = Map.empty
        let mapVariableToUniq kind =
            List.map (changeVariablesRecursive (fun (Variable(v)) ->
                let newName = v + (nextVarIdGetter(v, kind))
                let key = kind + "_" + newName
                initialVariableNameMap <- initialVariableNameMap.Add (key, v)
                VariableTerm(Variable(newName))
            ))
        let mapVariableBack =
            changeVariablesRecursive (fun (Variable(v)) ->
                let pKey = "parameters" + "_" + v
                let aKey = "arguments" + "_" + v
                initialVariableNameMap.TryFind pKey
                |> Option.orElse (initialVariableNameMap.TryFind aKey)
                |> Option.get
                |> Variable
                |> VariableTerm
            )
        
        let parameters = parameters |> Transformers.fromParams |> mapVariableToUniq "parameters" |> Transformers.toParams
        let arguments = arguments |> Transformers.fromArgs |> mapVariableToUniq "arguments" |> Transformers.toArgs
        
        unifyParamsWithArgs parameters arguments
        |> Option.map (List.map (fun (Unified(u)) -> u |> mapVariableBack))