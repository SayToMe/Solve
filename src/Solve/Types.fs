namespace Solve

open System.Diagnostics

module TermTypes =
    [<AutoOpen>]
    module Concrete =
        type AtomTerm = AtomTerm of string
        type BoolTerm = BoolTerm of bool
        type NumberTerm = NumberTerm of double
        type CharTerm = CharTerm of char
    
        and [<StructuredFormatDisplay("{AsString}")>] TypedTerm = TypedAtomTerm of AtomTerm | TypedBoolTerm of BoolTerm | TypedNumberTerm of NumberTerm | TypedCharTerm of CharTerm
        with
        member a.AsString =
            let rec formatTyped =
                function
                | TypedAtomTerm(AtomTerm v) -> v.ToString()
                | TypedBoolTerm(BoolTerm v) -> v.ToString()
                | TypedNumberTerm(NumberTerm v) -> v.ToString()
                | TypedCharTerm(CharTerm v) -> v.ToString()
            formatTyped a
        override a.ToString() = a.AsString

    [<AutoOpen>]
    module Variable =
        type AnonimVariable = AnonimVariable
        type Variable = Variable of string
        
    [<StructuredFormatDisplay("{AsString}")>]
    type Term = VariableTerm of Variable | TypedTerm of TypedTerm | StructureTerm of Structure | ListTerm of TypedListTerm
        with
        member a.AsString =
            match a with
            | VariableTerm(Variable(v)) -> "~" + v + "~"
            | TypedTerm(typed) -> typed.AsString
            | StructureTerm(Structure(functor', parameters)) -> functor' + "(" + (parameters |> List.fold (fun acc p -> if acc = "" then p.AsString else acc + ", " + p.AsString) "") + ")"
            | ListTerm(x) -> x.AsString
        override a.ToString() = a.AsString
    and Structure = Structure of string * Term list
    and TypedListTerm = | NilTerm | VarListTerm of Variable | TypedListTerm of Term * TypedListTerm
        with
        member a.AsString =
            match a with
            | NilTerm -> "[]"
            | VarListTerm(v) -> "[" + (VariableTerm(v).AsString) + "]"
            | TypedListTerm(head, rest) -> "[" + head.AsString + "," + (ListTerm(rest)).AsString
        override a.ToString() = a.AsString

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