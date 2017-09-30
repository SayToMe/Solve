namespace Solve

open System.Diagnostics

module Types =
    [<AutoOpen>]
    module Concrete =
        type SBool = SBool of bool
        type SNumber = SNumber of double
        type SChar = SChar of char
    
        type SList = SList of list<Typed>
        and Typed = TypedSBool of SBool | TypedSNumber of SNumber | TypedSChar of SChar | TypedSList of SList

    [<AutoOpen>]
    module Variable =
        type AnonimVariable = AnonimVariable
        type Variable = Variable of string
        
    [<StructuredFormatDisplay("{AsString}")>]
    type Any = AnyVariable of Variable | AnyTyped of Typed | AnyStruct of Struct
        with
        member a.AsString =
            match a with
            | AnyVariable(Variable(v)) -> "~" + v + "~"
            | AnyTyped(typed) ->
                let rec formatTyped = function
                                      | TypedSBool(SBool v) -> v.ToString()
                                      | TypedSNumber(SNumber v) -> v.ToString()
                                      | TypedSChar(SChar v) -> v.ToString()
                                      | TypedSList(SList v) when List.forall (function | TypedSChar (_) -> true | _ -> false) v -> "[" + (List.fold (fun acc s -> if acc = "" then formatTyped s else acc + formatTyped s) "" v) + "]"
                                      | TypedSList(SList v) -> "[" + (List.fold (fun acc s -> if acc = "" then formatTyped s else acc + ", " + formatTyped s) "" v) + "]"
                formatTyped typed
            | AnyStruct(Struct(functor, parameters)) -> functor + "(" + (parameters |> List.fold (fun acc p -> if acc = "" then p.AsString else acc + ", " + p.AsString) "") + ")"
    and Struct = Struct of string * Any list

    module Transformers =
        [<DebuggerStepThrough>]
        let sbool = SBool >> TypedSBool
        [<DebuggerStepThrough>]
        let strue = sbool true
        [<DebuggerStepThrough>]
        let sfalse = sbool false

        [<DebuggerStepThrough>]
        let snum = SNumber >> TypedSNumber
        [<DebuggerStepThrough>]
        let snum1 = snum 1.

        [<DebuggerStepThrough>]
        let schar = SChar >> TypedSChar
        [<DebuggerStepThrough>]
        let sstring v = TypedSChar <| SChar v
        
        [<DebuggerStepThrough>]
        let variable = Variable >> AnyVariable