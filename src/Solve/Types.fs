﻿namespace Solve

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
        member self.AsString =
            let rec formatTyped =
                function
                | TypedAtomTerm(AtomTerm atomTerm) -> atomTerm.ToString()
                | TypedBoolTerm(BoolTerm boolTerm) -> boolTerm.ToString()
                | TypedNumberTerm(NumberTerm numberTerm) -> numberTerm.ToString()
                | TypedCharTerm(CharTerm charTerm) -> charTerm.ToString()
            formatTyped self
        override self.ToString() = self.AsString

    [<AutoOpen>]
    module Variable =
        type AnonimVariable = AnonimVariable
        type Variable = Variable of name: string
        
    [<StructuredFormatDisplay("{AsString}")>]
    type Term = VariableTerm of Variable | TypedTerm of TypedTerm | StructureTerm of Structure | ListTerm of TypedListTerm
        with
        member self.AsString =
            match self with
            | VariableTerm(Variable(v)) -> "~" + v + "~"
            | TypedTerm(typed) -> typed.AsString
            | StructureTerm(Structure(functor', parameters)) ->
                functor' + "(" + (parameters |> List.fold (fun acc p -> if acc = "" then p.AsString else acc + ", " + p.AsString) "") + ")"
            | ListTerm(x) -> x.AsString
        override self.ToString() = self.AsString
    and Structure = Structure of string * Term list
    and TypedListTerm = | NilTerm | VarListTerm of Variable | TypedListTerm of Term * TypedListTerm
        with
        member self.asStringInner =
            match self with 
            | NilTerm -> "[]"
            | VarListTerm(v) -> " | " + (VariableTerm(v)).AsString
            | TypedListTerm(head, NilTerm) -> head.AsString
            | TypedListTerm(head, rest) -> head.AsString + ", " + rest.asStringInner           
        member self.AsString =
            match self with
            | NilTerm -> "[]"
            | VarListTerm(v) -> "[" + self.asStringInner + "]"
            | TypedListTerm(head, rest) -> "[" + self.asStringInner + "]"
        override self.ToString() = self.AsString

    module Helpers =
        [<DebuggerStepThrough>]
        let isVariable =
            function
            | VariableTerm _ -> true
            | _ -> false

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

        [<DebuggerStepThrough>]
        let atom = AtomTerm >> TypedAtomTerm >> TypedTerm

        [<DebuggerStepThrough>]
        let anyList =
            List.rev
            >> List.fold (fun st t -> TypedListTerm(t, st)) NilTerm
            >> ListTerm
        
        [<DebuggerStepThrough>]
        let anyListVar l v =
            l
            |> List.rev
            |> List.fold (fun st t -> TypedListTerm(t, st)) (VarListTerm (Variable v))
            |> ListTerm
        
        [<DebuggerStepThrough>]
        let numList =
            List.rev
            >> List.fold (fun st t -> TypedListTerm(num t, st)) NilTerm
            >> ListTerm
        
        [<DebuggerStepThrough>]
        let rec stringList (str: string) = 
            let rec strImpl idx =
                if idx >= str.Length then
                    NilTerm
                else
                    TypedListTerm(TypedTerm(TypedCharTerm(CharTerm(str.[idx]))), strImpl (idx + 1))
            ListTerm(strImpl 0)

        let anyStruct name args =
            StructureTerm(Structure(name, args))
            
        let rec anyListToConcreteTerms (list: TypedListTerm) =
            match list with 
            | NilTerm -> []
            | VarListTerm _ -> failwith "Unexpected end of list"
            | TypedListTerm(head, tail) -> head::anyListToConcreteTerms tail