namespace Solve

open Types

open Rule

module VariableUnify =
    let processStruct changeVariable (Struct(functor, prms)) =
        let changeIfVariable =
            function
            | AnyVariable(v) -> changeVariable v
            | a -> a
        Struct(functor, prms |> List.map changeIfVariable)

    let rec unifyTwoAny v1 v2 =
        match (v1, v2) with
        | (AnyVariable(_), AnyVariable(_)) -> Some v1
        | (AnyVariable(_), AnyTyped(_)) -> Some v2
        | (AnyVariable(_), AnyStruct(_)) -> Some v2
        | (AnyTyped(_), AnyVariable(_)) -> Some v1
        | (AnyStruct(_), AnyVariable(_)) -> Some v1
        | (AnyTyped(vt1), AnyTyped(vt2)) when vt1 = vt2 -> Some v2
        | (AnyStruct(Struct(f1, p1)), AnyStruct(Struct(f2, p2))) when f1 = f2 && p1.Length = p2.Length ->
            let newArgs = List.map2 (fun v1 v2 -> unifyTwoAny v1 v2) p1 p2
            if List.exists Option.isNone newArgs then
                None
            else
                let newArgs = newArgs |> List.map Option.get
                Some(AnyStruct(Struct(f1, newArgs)))
        | _ -> None
        
    let postUnifyUnaryExpressions v1 v2 fn v =
        if AnyVariable(v) = v1 then 
            v2 
        else 
            fn v

    let postUnifyBinaryExpression proc functor e1 e2 =
        match (e1, e2) with
        | (AnyVariable(v1), AnyVariable(v2)) -> functor(proc v1, proc v2)
        | (AnyVariable(v1), AnyTyped(_)) -> functor(proc v1, e2)
        | (AnyVariable(v1), AnyStruct(v2)) -> functor(proc v1, AnyStruct(processStruct proc v2))
        | (AnyTyped(_), AnyVariable(v2)) -> functor(e1, proc v2)
        | (AnyStruct(v1), AnyVariable(v2)) -> functor(AnyStruct(processStruct proc v1), proc v2)
        | _ -> functor(e1, e2)

    let postUnifyBinaryExpressions (v1, v2) (v3, v4) fn v =
        if AnyVariable(v) = v1 then
            v3 
        else if AnyVariable(v) = v2 then 
            v4 
        else fn v
        
    let rec unifyParamsWithArguments parameters arguments =
        let prms = List.map2 (fun (Parameter(p)) (Argument(a)) -> unifyTwoAny p a) parameters arguments
        if List.exists Option.isNone prms then
            None
        else
            Some <| List.map Option.get prms