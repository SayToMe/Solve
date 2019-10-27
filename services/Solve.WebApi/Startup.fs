namespace Solve.WebApi

open System
open System.Collections.Generic
open System.Linq
open System.Threading.Tasks
open Microsoft.AspNetCore.Builder
open Microsoft.AspNetCore.Hosting
open Microsoft.Extensions.Configuration
open Microsoft.Extensions.DependencyInjection

type Startup private () =
    new (configuration: IConfiguration) as this =
        Startup() then
        this.Configuration <- configuration

    member this.ConfigureServices(services: IServiceCollection) =
        services.AddMemoryCache() |> ignore

        services
            .AddMvcCore(fun options ->
                options.RequireHttpsPermanent <- true
                options.RespectBrowserAcceptHeader <- true
            )
            .AddFormatterMappings()
            .AddJsonOptions(fun v -> v |> ignore)
        |> ignore

    member this.Configure(app: IApplicationBuilder, env: IWebHostEnvironment) =
        app.UseMvc() |> ignore

    member val Configuration : IConfiguration = null with get, set