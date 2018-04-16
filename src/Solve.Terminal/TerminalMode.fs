namespace Solve.Terminal

open System

[<StructuredFormatDisplay("{AsString}")>]
type TerminalMode =
    | Welcome
    | Insert
    | Query
    | Exit
    | End
    with
    member self.AsString =
        match self with
        | Welcome -> "Welcome to terminal. Choose mode by typing: 'insert' (:-) or 'query' (?-)."
        | Insert -> ":-"
        | Query -> "?-"
        | Exit -> "Exit..."
        | End -> failwith "Should not be called"
