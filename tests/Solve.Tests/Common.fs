module Solve.Tests.Common

open NUnit.Framework
open System.Diagnostics

open Solve

open TermTypes
open TermTypes.Transformers

open Rule
open Rule.Transformers

[<DebuggerStepThrough>]
let inline fail() = failwith ""
[<DebuggerStepThrough>]
let inline check (expected: 'a) (actual: 'a) = 
    Assert.AreEqual(expected, actual, sprintf "%O != %O" expected actual)
[<DebuggerStepThrough>]
let inline checkExecuteExpression expected actual =
    check expected (Seq.toList actual)
[<DebuggerStepThrough>]
let inline checkSolve expected actual =
    check expected (actual |> Seq.map (Seq.toList) |> Seq.toList)

[<DebuggerStepThrough>]
let inline SIGNATURE name terms = Signature(name, toParams terms)
[<DebuggerStepThrough>]
let inline RULE signature body = Rule(signature, body)
[<DebuggerStepThrough>]
let inline FACT signature = Rule(signature, True)
[<DebuggerStepThrough>]
let inline GOAL name terms = CallExpression(GoalSignature(name, toArgs terms))
