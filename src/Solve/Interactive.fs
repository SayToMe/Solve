namespace Solve

open Microsoft.FSharp.Text.Lexing

type Interactive() =
    let mutable _knowledgebase = []

    member self.NewInput text =
        let lexbuf = LexBuffer<char>.FromString text

        let countFromParser = PrologParser.start PrologLexer.read lexbuf
        _knowledgebase <- countFromParser :: _knowledgebase

        countFromParser