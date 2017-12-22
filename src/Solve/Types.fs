namespace Solve

open System.Diagnostics

module TermTypes =
    [<AutoOpen>]
    module Concrete =
        type AtomTerm = AtomTerm of string
        type BoolTerm = BoolTerm of bool
        type NumberTerm = NumberTerm of double
        type CharTerm = CharTerm of char
    
        type ListTerm = ListTerm of list<TypedTerm>
        and [<StructuredFormatDisplay("{AsString}")>] TypedTerm = TypedAtomTerm of AtomTerm | TypedBoolTerm of BoolTerm | TypedNumberTerm of NumberTerm | TypedCharTerm of CharTerm | TypedListTerm of ListTerm
        with
        member a.AsString =
            let rec formatTyped =
                function
                | TypedAtomTerm(AtomTerm v) -> v.ToString()
                | TypedBoolTerm(BoolTerm v) -> v.ToString()
                | TypedNumberTerm(NumberTerm v) -> v.ToString()
                | TypedCharTerm(CharTerm v) -> v.ToString()
                | TypedListTerm(ListTerm v) when List.forall (function | TypedCharTerm (_) -> true | _ -> false) v -> "[" + (List.fold (fun acc s -> if acc = "" then formatTyped s else acc + formatTyped s) "" v) + "]"
                | TypedListTerm(ListTerm v) -> "[" + (List.fold (fun acc s -> if acc = "" then formatTyped s else acc + ", " + formatTyped s) "" v) + "]"
            formatTyped a
        override a.ToString() = a.AsString

    [<AutoOpen>]
    module Variable =
        type AnonimVariable = AnonimVariable
        type Variable = Variable of string
        
    [<StructuredFormatDisplay("{AsString}")>]
    type Term = VariableTerm of Variable | TypedTerm of TypedTerm | StructureTerm of Structure
        with
        member a.AsString =
            match a with
            | VariableTerm(Variable(v)) -> "~" + v + "~"
            | TypedTerm(typed) -> typed.AsString
            | StructureTerm(Structure(functor', parameters)) -> functor' + "(" + (parameters |> List.fold (fun acc p -> if acc = "" then p.AsString else acc + ", " + p.AsString) "") + ")"
        override a.ToString() = a.AsString
    and Structure = Structure of string * Term list

    module Transformers =
        [<DebuggerStepThrough>]
        let bool = BoolTerm >> TypedBoolTerm >> TypedTerm

        [<DebuggerStepThrough>]
        let num = NumberTerm >> TypedNumberTerm >> TypedTerm

        [<DebuggerStepThrough>]
        let char = CharTerm >> TypedCharTerm >> TypedTerm
        [<DebuggerStepThrough>]
        let string = CharTerm >> TypedCharTerm >> TypedTerm
        
        [<DebuggerStepThrough>]
        let var = Variable >> VariableTerm