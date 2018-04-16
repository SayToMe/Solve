namespace Solve.Terminal

open Solve
open Solve.Rule
open Solve.PrologParser
open Solve.PrologParser.Parser

open System

type ITerminal =
    abstract member Solve: Goal -> string seq
    abstract member Insert: Rule -> unit
    abstract member Log: LogMessage -> unit
    abstract member ReadInput: unit -> string
    abstract member ReadKey: unit -> ConsoleKeyInfo

[<AutoOpen>]
module TerminalRunners =
    let getBacktrackMode (terminal: ITerminal) =
        BackTrackMode.Parse(terminal.ReadKey())

    let showResult (result: string seq) (showRes: string -> unit) (getBacktrackMode: unit -> BackTrackMode) =
        result
        |> Seq.unfold (
            fun st ->
            match Seq.tryHead st with
            | Some answ ->
                let showAnswer answ = if answ = "" then showRes "true" else showRes (sprintf "%A" answ)

                showAnswer answ

                let backtrackMode = getBacktrackMode()
                match backtrackMode with
                | SingleBackTrack -> Some (answ, Seq.tail st)
                | AlwaysBackTrack -> 
                    Seq.iter showAnswer (Seq.tail st)
                    showRes "false"
                    None
                | NoBackTrack -> None
            | _ ->
                showRes "false"
                None
        )
        |> Seq.iter ignore

    let consumeInput (terminal: ITerminal) (mode: TerminalMode) (input: string) =
        let fullPlString = mode.AsString + input
        match parsePlString fullPlString with
        | RuleParseResult rule -> 
            terminal.Insert rule
        | CallParseResult goal ->
            let res = terminal.Solve (Goal(goal))
            terminal.Log (ResultLog res)
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

                match terminal.ReadInput() with
                | "exit"
                | "e"
                | "q"
                | "quit" -> Exit
                | "?-"
                | "query" -> Query
                | ":-"
                | "insert" -> Insert
                | input ->
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