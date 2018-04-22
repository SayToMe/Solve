namespace Solve.WebApi.Controllers

open System
open System.Collections.Generic
open System.Linq
open System.Threading.Tasks
open Microsoft.AspNetCore.Mvc

open Solve.Rule
open Solve.Rule.Transformers
open Solve.TermTypes.Transformers
open Solve.Terminal

open Microsoft.Extensions.Caching.Distributed
open Microsoft.Extensions.Caching.Redis
open Microsoft.Extensions.Caching.Memory

type WebTerminal() as self =
    let kb = MutableKnowledgebase([])
    let kbw = kb :> IKnowledgebaseWrapper

    let getBacktrackMode () =
        Solve.Terminal.TerminalRunners.getBacktrackMode self

    member __.GetRules = kb.Rules

    interface ITerminal with
        member __.Solve goal = kbw.Solve goal
        member __.Insert rule = kbw.AddRule rule
        member __.Log logMessage =
            match logMessage with
            | ModeLog mode -> printf "%s" mode.AsString
            | InfoLog info -> printfn "%s" info
            | SuccessInsertionLog(name, arity) -> printfn "Success insertion of %s/%i" name arity
            | ResultLog res -> showResult res (printfn "%s") getBacktrackMode
            | ErrorLog error -> printfn "Error: %s" error
        member __.ReadInput() = Console.ReadLine()
        member __.ReadKey() = Console.ReadKey()

module RuleCacheExtensions =
    let getWebTerminal (mem: IMemoryCache) =
        mem.GetOrCreate("terminal", fun _ -> WebTerminal())

    let getTerminal (mem: IMemoryCache) =
        mem.GetOrCreate("terminal", fun _ -> WebTerminal()) :> ITerminal

[<Route("api/[controller]")>]
type SolveController (memCache: IMemoryCache) =
    inherit Controller()

    [<HttpGet>]
    member this.Get() =
        RuleCacheExtensions.getWebTerminal memCache
        |> (fun wt -> wt.GetRules)
        |> sprintf "%A"

    [<HttpPost>]
    member this.Post([<FromBody>]plCode: string) =
        match Solve.Terminal.TerminalRunners.getConsumedInput (RuleCacheExtensions.getTerminal memCache) plCode with
        | Some(v) -> v
        | None -> ErrorLog "No result"
