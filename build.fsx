// --------------------------------------------------------------------------------------
// FAKE build script
// --------------------------------------------------------------------------------------
#r "paket: groupref FakeBuild //"

#load "./.fake/build.fsx/intellisense.fsx"

open System.IO
open Fake.Core
open Fake.Core.TargetOperators
open Fake.DotNet
open Fake.IO
open Fake.IO.FileSystemOperators
open Fake.IO.Globbing.Operators
open Fake.DotNet.Testing
open Fake.Tools
open Fake.Api

// --------------------------------------------------------------------------------------
// START TODO: Provide project-specific details below
// --------------------------------------------------------------------------------------

// Information about the project are used
//  - for version and project name in generated AssemblyInfo file
//  - by the generated NuGet package
//  - to run tests and to publish documentation on GitHub gh-pages
//  - for documentation, you also need to edit info in "docsrc/tools/generate.fsx"

// The name of the project
// (used by attributes in AssemblyInfo, name of a NuGet package and directory in 'src')
let project = "Solve"

// Short summary of the project
// (used as description in AssemblyInfo and as a short summary for NuGet package)
let summary = "Prolog F# implementation"

// Longer description of the project
// (used as a description for NuGet package; line breaks are automatically cleaned up)
let description = "Library for Prolog emulation"

// List of author names (for NuGet package)
let authors = [ "qrtic" ]

// Tags for your project (for NuGet package)
let tags = "prolog"

// File system information
let solutionFile  = "Solve.sln"

// Default Target.create configuration
let configuration = "Release"

// Pattern specifying assemblies to be tested using NUnit
let testAssembly = "tests/Solve.Tests"

// Default test framework
let testFramework = "netcoreapp3.0"

// Git configuration (used for publishing documentation in gh-pages branch)
// The profile where the project is posted
let gitOwner = "Qrtic"
let gitHome = sprintf "%s/%s" "https://github.com" gitOwner

// The name of the project on GitHub
let gitName = "Solve"

// The url for the raw files hosted
let gitRaw = Environment.environVarOrDefault "gitRaw" "https://raw.githubusercontent.com/Qrtic"

// --------------------------------------------------------------------------------------
// END TODO: The rest of the file includes standard build steps
// --------------------------------------------------------------------------------------

// Read additional information from the release notes document
let release = ReleaseNotes.load "RELEASE_NOTES.md"

// Helper active pattern for project types
let (|Fsproj|Csproj|Vbproj|Shproj|) (projFileName:string) =
    match projFileName with
    | f when f.EndsWith("fsproj") -> Fsproj
    | f when f.EndsWith("csproj") -> Csproj
    | f when f.EndsWith("vbproj") -> Vbproj
    | f when f.EndsWith("shproj") -> Shproj
    | _                           -> failwith (sprintf "Project file %s not supported. Unknown project type." projFileName)

// Generate assembly info files with the right version & up-to-date information
Target.create "AssemblyInfo" (fun _ ->
    let getAssemblyInfoAttributes projectName =
        [ AssemblyInfo.Title (projectName)
          AssemblyInfo.Product project
          AssemblyInfo.Description summary
          AssemblyInfo.Version release.AssemblyVersion
          AssemblyInfo.FileVersion release.AssemblyVersion
          AssemblyInfo.Configuration configuration ]

    let getProjectDetails projectPath =
        let projectName = System.IO.Path.GetFileNameWithoutExtension(projectPath)
        ( projectPath,
          projectName,
          System.IO.Path.GetDirectoryName(projectPath),
          (getAssemblyInfoAttributes projectName)
        )

    !! "src/**/*.??proj"
    |> Seq.map getProjectDetails
    |> Seq.iter (fun (projFileName, _, folderName, attributes) ->
        match projFileName with
        | Fsproj -> AssemblyInfoFile.createCSharp (folderName </> "AssemblyInfo.fs") attributes
        | Csproj -> AssemblyInfoFile.createCSharp ((folderName </> "Properties") </> "AssemblyInfo.cs") attributes
        | _ -> ()
        )
)

// Copies binaries from default VS location to expected bin folder
// But keeps a subdirectory structure for each project in the
// src folder to support multiple project outputs
Target.create "CopyBinaries" (fun _ ->
    !! "src/**/*.??proj"
    -- "src/**/*.shproj"
    |>  Seq.map (fun f -> ((System.IO.Path.GetDirectoryName f) </> "bin" </> configuration, "bin" </> (System.IO.Path.GetFileNameWithoutExtension f)))
    |>  Seq.iter (fun (fromDir, toDir) -> Shell.copyDir toDir fromDir (fun _ -> true))
)

// --------------------------------------------------------------------------------------
// Clean build results

let vsProjProps = 
    [ ("Configuration", configuration); ("Platform", "Any CPU") ]

Target.create "Clean" (fun _ ->
    Shell.cleanDirs ["bin"; "temp"; "tests/coveragereport"; "tests/report"]
)

Target.create "CleanDocs" (fun _ ->
    Shell.cleanDirs ["docs"]
)

// --------------------------------------------------------------------------------------
// Restore nuget

Target.create "Restore" (fun _ ->
    solutionFile
    |> DotNet.restore id
)

// --------------------------------------------------------------------------------------
// Build library & test project

Target.create "Build" (fun _ ->
    solutionFile
    |> DotNet.build (fun c ->
        { c with
            Configuration = DotNet.BuildConfiguration.Custom(configuration)
        }
    )
)

// --------------------------------------------------------------------------------------
// Run the unit tests using test runner

Target.create "RunTests" (fun _ ->
    let assemblies = [testAssembly]

    let setParams assembly info =
        { info with
            FileName = "dotnet"
            Arguments = "test /p:CollectCoverage=true /p:CoverletOutputFormat=opencover"
            WorkingDirectory = assembly
        }
    assemblies
    |> Seq.map (fun assembly ->
        Process.execSimple (setParams assembly) System.TimeSpan.MaxValue
    )
    |>Seq.reduce (+)
    |> (fun i -> if i > 0 then failwith "")
)

Target.create "CoverageReport" (fun _ ->
    let assemblies = [testAssembly]

    let setParams assembly info =
        { info with
            FileName = "dotnet"
            Arguments = "reportgenerator -reports:coverage.opencover.xml -targetdir:coveragereport -reporttypes:HTML"
            WorkingDirectory = assembly
        }
    assemblies
    |> Seq.iter (fun assembly ->
        Process.execSimple (setParams assembly) System.TimeSpan.MaxValue |> ignore
    )
)

// --------------------------------------------------------------------------------------
// Build a NuGet package

Target.create "NuGet" (fun _ ->
    Paket.pack(fun p ->
        { p with
            OutputPath = "bin"
            Version = release.NugetVersion
            ReleaseNotes = String.toLines release.Notes})
)

Target.create "PublishNuget" (fun _ ->
    Paket.push(fun p ->
        { p with
            PublishUrl = "https://www.nuget.org"
            WorkingDir = "bin" })
)

// --------------------------------------------------------------------------------------
// Generate the documentation

// Paths with template/source/output locations
let bin        = __SOURCE_DIRECTORY__ @@ "bin"
let content    = __SOURCE_DIRECTORY__ @@ "docsrc/content"
let output     = __SOURCE_DIRECTORY__ @@ "docs"
let files      = __SOURCE_DIRECTORY__ @@ "docsrc/files"
let templates  = __SOURCE_DIRECTORY__ @@ "docsrc/tools/templates"
let formatting = __SOURCE_DIRECTORY__ @@ "packages/formatting/FSharp.Formatting"
let docTemplate = "docpage.cshtml"

let github_release_user = Environment.environVarOrDefault "github_release_user" gitOwner
let githubLink = "https://github.com/Qrtic/solve"

// Specify more information about your project
let info =
  [ "project-name", project
    "project-author", authors |> Seq.head
    "project-summary", summary
    "project-github", githubLink
    "project-nuget", "http://nuget.org/packages/Solve" ]

let root = githubLink

let referenceBinaries = []

let layoutRootsAll = new System.Collections.Generic.Dictionary<string, string list>()
layoutRootsAll.Add("en",[   templates;
                            formatting @@ "templates"
                            formatting @@ "templates/reference" ])

// Target.create "ReferenceDocs" (fun _ ->
//     Directory.ensure (output @@ "reference")

//     let binaries () =
//         let manuallyAdded =
//             referenceBinaries
//             |> List.map (fun b -> bin @@ b)

//         let conventionBased =
//             DirectoryInfo bin
//             |> DirectoryInfo.getSubDirectories
//             |> Array.collect (fun d ->
//                 let opt =
//                     let frameworks = ["net45";"net47";"netstandard2.0";"netcoreapp2.0"]

//                     frameworks
//                     |> List.map (fun f -> f, DirectoryInfo.getSubDirectories d |> Array.filter(fun x -> x.FullName.ToLower().Contains(f)))
//                     |> List.filter (fun (_, d) -> d.Length > 0)
//                     |> fun l -> if l.Length > 0 then Some l.Head else None

//                 opt
//                 |> Option.map (fun (name, dInfo) ->
//                     dInfo
//                     |> Array.collect (fun d -> d.GetFiles())
//                     |> Array.filter (fun x ->
//                         x.Name.ToLower() = (sprintf "%s.dll" name).ToLower())
//                     |> Array.map (fun x -> x.FullName))
//                 |> Option.defaultValue Array.empty)
//             |> List.ofArray

//         conventionBased @ manuallyAdded

//     binaries()
//     |> FSFormatting.createDocsForDlls (fun args ->
//         { args with
//             OutputDirectory = output @@ "reference"
//             LayoutRoots =  layoutRootsAll.["en"]
//             ProjectParameters =  ("root", root)::info
//             SourceRepository = githubLink @@ "tree/master" }
//            )
// )

let copyFiles () =
    Shell.copyRecursive files output true
    |> Trace.logItems "Copying file: "
    Directory.ensure (output @@ "content")
    Shell.copyRecursive (formatting @@ "styles") (output @@ "content") true
    |> Trace.logItems "Copying styles and scripts: "

Target.create "Docs" (fun _ ->
    File.delete "docsrc/content/release-notes.md"
    Shell.copyFile "docsrc/content/" "RELEASE_NOTES.md"
    Shell.rename "docsrc/content/release-notes.md" "docsrc/content/RELEASE_NOTES.md"

    File.delete "docsrc/content/license.md"
    Shell.copyFile "docsrc/content/" "LICENSE.txt"
    Shell.rename "docsrc/content/license.md" "docsrc/content/LICENSE.txt"


    DirectoryInfo.getSubDirectories (DirectoryInfo.ofPath templates)
    |> Seq.iter (fun d ->
                    let name = d.Name
                    if name.Length = 2 || name.Length = 3 then
                        layoutRootsAll.Add(
                                name, [templates @@ name
                                       formatting @@ "templates"
                                       formatting @@ "templates/reference" ]))
    copyFiles ()

    for dir in  [ content; ] do
        let langSpecificPath(lang, path:string) =
            path.Split([|'/'; '\\'|], System.StringSplitOptions.RemoveEmptyEntries)
            |> Array.exists(fun i -> i = lang)
        let layoutRoots =
            let key = layoutRootsAll.Keys |> Seq.tryFind (fun i -> langSpecificPath(i, dir))
            match key with
            | Some lang -> layoutRootsAll.[lang]
            | None -> layoutRootsAll.["en"] // "en" is the default language

        FSFormatting.createDocs (fun args ->
            { args with
                Source = content
                OutputDirectory = output
                LayoutRoots = layoutRoots
                ProjectParameters  = ("root", root)::info
                Template = docTemplate } )
)

// --------------------------------------------------------------------------------------
// Release Scripts

Target.create "Release" (fun _ ->
    Git.Staging.stageAll ""
    Git.Commit.exec "" (sprintf "Bump version to %s" release.NugetVersion)
    Git.Branches.push ""

    Git.Branches.tag "" release.NugetVersion
    Git.Branches.pushTag "" "origin" release.NugetVersion
)

Target.create "BuildPackage" ignore
Target.create "GenerateDocs" ignore

// --------------------------------------------------------------------------------------
// Run all targets by default. Invoke 'build <Target>' to override

Target.create "All" ignore

"Clean"
  ==> "AssemblyInfo"
  ==> "Restore"
  ==> "Build"
  ==> "CopyBinaries"
  ==> "RunTests"
  ==> "CoverageReport"
//   ==> "GenerateDocs"
  ==> "NuGet"
  ==> "BuildPackage"
  ==> "All"

"RunTests" ?=> "CleanDocs"

"CleanDocs"
  ==>"Docs"
//   ==> "ReferenceDocs"
  ==> "GenerateDocs"

"Clean"
  ==> "Release"

"BuildPackage"
  ==> "PublishNuget"
  ==> "Release"

Target.runOrDefault "All"
