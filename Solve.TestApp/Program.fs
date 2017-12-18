// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.

open Solve

open TermTypes
open TermTypes.Transformers

open Rule
open Rule.Transformers

[<EntryPoint>]
let main argv = 
    let i = Solve.Interactive()

    let mutable input = System.Console.ReadLine()
    while input <> "exit" do
        try
            i.NewInput input |> printfn "%d"
        with
        | _ as e -> printfn "Failed to parse previous input"

        input <- System.Console.ReadLine()

    0 // return an integer exit code
