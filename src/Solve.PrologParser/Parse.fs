namespace Solve.PrologParser

open FParsec

open Solve.PrologParser.Primitives

module Parser =
    let convertResult = function
       | Success(r, _, _) -> r
       | Failure(e, _, _) -> ParseError e

    let testRun parser str =
        run parser str

    let testRunConvert parser str =
        testRun parser str
        |> convertResult

    let parsePlString str =
        run pcommand str
        |> convertResult
    
    //// UTF8 is the default, but it will detect UTF16 or UTF32 byte-order marks automatically
    //let parsePlFile fileName encoding =
    //    runParserOnFile pcommand () fileName encoding
    //    |> convertResult
    
    //let parsePlStream stream encoding =
        //runParserOnStream pcommand () "" stream System.Text.Encoding.UTF8
        //|> convertResult
