namespace Solve

open Microsoft.FSharp.Text.Lexing

module Parse =
    let parse (str: string) =
        let lexbuf = LexBuffer<char>.FromString str

        PrologParser.start PrologLexer.read lexbuf
