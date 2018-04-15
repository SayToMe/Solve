namespace Solve.Terminal

open Solve
open Solve.Rule
open Solve.PrologParser
open Solve.PrologParser.Parser

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

type BackTrackMode =
    | NoBackTrack
    | SingleBackTrack
    | AlwaysBackTrack
    with
        static member Parse (keyInfo: ConsoleKeyInfo) =
            match keyInfo.Key with
            | ConsoleKey.Escape -> NoBackTrack
            | ConsoleKey.Spacebar
            | ConsoleKey.Enter -> SingleBackTrack
            | ConsoleKey.A -> AlwaysBackTrack
            | _ ->
                match keyInfo.KeyChar with
                | ';' -> SingleBackTrack
                | '.' -> NoBackTrack
                | _ -> SingleBackTrack

type LogMessage =
    | ModeLog of TerminalMode
    | SuccessInsertionLog of string * int
    | ResultLog of string
    | ErrorLog of string
    | InfoLog of string

type ITerminal =
    abstract member Solve: Goal -> string seq
    abstract member Insert: Rule -> unit
    abstract member Log: LogMessage -> unit
    abstract member ReadInput: unit -> string
    abstract member ReadKey: unit -> ConsoleKeyInfo

[<AutoOpen>]
module TerminalRunners =
    let consumeInput (terminal: ITerminal) (mode: TerminalMode) (input: string) =
        let fullPlString = mode.AsString + input
        match parsePlString fullPlString with
        | RuleParseResult rule -> 
            terminal.Insert rule
        | CallParseResult goal ->
            terminal.Solve (Goal(goal))
            |> Seq.unfold (fun st ->
                match Seq.tryHead st with
                | Some answ ->
                    let showAnswer answ = if answ = "" then terminal.Log (ResultLog "true") else terminal.Log (ResultLog (sprintf "%A" answ))

                    showAnswer answ

                    let backtrackMode = BackTrackMode.Parse(terminal.ReadKey())
                    match backtrackMode with
                    | SingleBackTrack -> Some (answ, Seq.tail st)
                    | AlwaysBackTrack -> 
                        Seq.iter showAnswer (Seq.tail st)
                        printfn "false"
                        None
                    | NoBackTrack -> None
                | _ ->
                    terminal.Log (ResultLog "false")
                    None
            )
            |> Seq.iter ignore
        | ParseError error ->
            terminal.Log (ErrorLog error)

    let run (terminal: ITerminal) (mode: TerminalMode) =
        match mode with
        | Welcome ->
            terminal.Log (InfoLog mode.AsString)
            Insert
        | Insert
        | Query ->
            try
                terminal.Log (ModeLog mode)

                let input = terminal.ReadInput()
                match input with
                | "exit"
                | "e"
                | "q" ->
                    Exit
                | _ ->
                    consumeInput terminal mode input
                    mode
            with
            | _ as e ->
                printfn "Failure. %A" e.Message
                mode
        | Exit ->
            terminal.Log (InfoLog mode.AsString)
            End
        | End -> failwith "Should not be called"