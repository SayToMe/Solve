namespace Solve.Parse

open FParsec

open Solve.Parse.Primitives

module Parse =
    let convertResult = function
       | Success(r, _, _) -> r
       | Failure(e, _, _) -> ParseError e

    let testRun parser str =
        run parser str

    let testRunConvert parser str =
        run parser str
        |> convertResult

    let parsePlString str =
        run pcommand str
        |> convertResult
    
    // UTF8 is the default, but it will detect UTF16 or UTF32 byte-order marks automatically
    let parsePlFile fileName encoding =
    #if PCL_FPARSEC
        runParserOnString pinteractive () fileName (System.IO.File.ReadAllText(fileName, encoding))
        |> convertResult
    #else
        runParserOnFile pcommand () fileName encoding
        |> convertResult
    #endif
    
    let parsePlStream stream encoding =
        runParserOnStream pcommand () "" stream System.Text.Encoding.UTF8
        |> convertResult
