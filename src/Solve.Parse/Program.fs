open System

let inline parse str = 
    printfn "Parsing: %A" str
    Solve.Parse.Parse.parsePlString str

[<EntryPoint>]
let main argv =
    printfn "Enter Prolog expression to be parsed"
    
    (Console.ReadLine ())
    |> parse
    |> printfn "%A"
    0
