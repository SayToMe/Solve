namespace Solve.Terminal

type LogMessage =
    | ModeLog of TerminalMode
    | SuccessInsertionLog of string * int
    | ResultLog of string seq
    | ErrorLog of string
    | InfoLog of string
