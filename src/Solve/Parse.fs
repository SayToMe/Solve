namespace Solve

open Microsoft.FSharp.Text.Lexing

module Parse =
    let parse str =
        let lexbuf = LexBuffer<char>.FromString str

        PrologParser.start PrologLexer.read lexbuf
