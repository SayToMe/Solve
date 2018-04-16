namespace Solve.Terminal

open System

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
