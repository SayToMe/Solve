namespace Solve.Parse

open Solve
open Solve.Rule.Transformers

open FParsec

open Solve.TermTypes

open Solve.Rule

type ParseResult =
    | RuleParseResult of Rule
    | CallParseResult of Expression
    | ParseError of string

module Prims =
    let ws = spaces // skips any whitespace
    let str = pstring

    let (<!>) (p: Parser<_,_>) label : Parser<_,_> =
        fun stream ->
            printfn "%A: Entering %s" stream.Position label
            let reply = p stream
            printfn "%A: Leaving %s (%A). Res: %A" stream.Position label reply.Status (reply.Result)
            reply

    let listBetweenStrings sOpen sClose pElement f =
        between (str sOpen) (str sClose)
                (ws >>. sepBy (pElement .>> ws) (str "," .>> ws) |>> f)
    
    let listBetweenStringsCustom sOpen sClose separatorParser pElement f =
        pipe3 (sOpen .>> ws) (ws >>. sepBy (pElement .>> ws) (separatorParser .>> ws)) (sClose .>> ws) f

    let ptrue () = stringReturn "true"  (TypedTerm <| TypedBoolTerm(BoolTerm(true)))
    let pfalse () = stringReturn "false" (TypedTerm <| TypedBoolTerm(BoolTerm(false)))
    let pnil () = stringReturn "[]" (ListTerm <| NilTerm)
    let pnumber () = pfloat |>> (TypedTerm << TypedNumberTerm << NumberTerm)
    let pchar () = attempt <| str "'" >>. anyChar .>> str "'" |>> (TypedTerm << TypedCharTerm << CharTerm)

    let patomPlain () =
        let isIdentifierFirstChar c = isLetter c && not(isUpper c)
        let isIdentifierChar c = isLetter c || isDigit c || c = '_'
    
        many1Satisfy2L isIdentifierFirstChar isIdentifierChar "identifier"
        .>> spaces
    let patom () =
        patomPlain ()
        |>> (TypedTerm << TypedAtomTerm << AtomTerm)
    let pvariablePlain () =
        let isIdentifierFirstChar c = isLetter c && isUpper c
        let isIdentifierChar c = isLetter c || isDigit c || c = '_'
    
        many1Satisfy2L isIdentifierFirstChar isIdentifierChar "identifier"
        .>> spaces
    let pvariable () =
        pvariablePlain ()
        |>> (VariableTerm << Variable)
 
    let pterm () = 
        let _pterm () = (patom () <|> pvariable () <|> pnumber () <|> pnil () <|> pfalse () <|> ptrue () <|> pchar ())
        
        let pstructure () = attempt <| pipe2 (patomPlain ()) (listBetweenStrings "(" ")" (_pterm ()) id) (fun atom terms ->
            Structure(atom, terms )) |>> StructureTerm
        let plist () =
            let pempty () = attempt (pnil ())
            let pnormalList () = attempt <| listBetweenStrings "[" "]" (_pterm ()) (List.rev >> List.fold (fun acc s -> TypedListTerm(s, acc)) NilTerm >> ListTerm)
            let pvariableList () = attempt <| listBetweenStringsCustom (str "[") (str "|" >>. ws >>. pvariablePlain () .>> ws .>> str "]") (str ",") (_pterm ()) (fun s terms var -> (VarListTerm(Variable(var)), terms |> List.rev) ||> List.fold (fun acc s -> TypedListTerm(s, acc)) |> ListTerm)

            attempt <| (pempty() <|> pnormalList () <|> pvariableList ())
        _pterm () <|> pstructure () <|> plist ()

    let psignature () =
        pipe2 (patomPlain ()) (listBetweenStrings "(" ")" (pterm ()) id) (fun atom terms ->
            Signature(atom, Transformers.toParams terms ))

    let pfact () = psignature () .>> pstring "." |>> (fun s -> Rule(s, True))

    let pbody () =
        let pcalc () =
            let rec _pcalc() =
                let pval = pterm () |>> Value
                let plus = pipe3 (_pcalc()) (pstring "+") (_pcalc()) (fun c1 _ c2 -> Plus(c1, c2))
                pval <|> plus
            _pcalc()
        let rec _pbody acceptInnerBody () =
            let ptrueExpr () = stringReturn "true" True
            let pfalseExpr () = stringReturn "false" False
            let peqExpr () = attempt <| pipe3 (pterm ()) (pstring "=") (pterm ()) (fun a1 _ a2 -> EqExpr(a1, a2))
            let pgrExpr () = attempt <| pipe3 (pterm ()) (pstring ">") (pterm ()) (fun a1 _ a2 -> GrExpr(a1, a2))
            let pleExpr () = attempt <| pipe3 (pterm ()) (pstring "<") (pterm ()) (fun a1 _ a2 -> LeExpr(a1, a2))
            let calcExpr () = attempt <| pipe3 (pterm ()) (pstring "is") (pcalc ()) (fun t _ c -> CalcExpr(t, c))
            let pandExpr () = attempt <| pipe3 (_pbody false ()) (pstring ",") (_pbody false ()) (fun expr1 _ expr2 -> AndExpression(expr1, expr2))
            let porExpr () = attempt <| pipe3 (_pbody false ()) (pstring ";") (_pbody false ()) (fun expr1 _ expr2 -> OrExpression(expr1, expr2))
            let pinnerExpr () = attempt <| (_pbody false ()) >>=? (fun x ->
                    ((pstring ",") >>? _pbody true () |>> (fun y -> AndExpression(x, y)))
                    <|>
                    ((pstring ";") >>? _pbody true () |>> (fun y -> OrExpression(x, y)))
                )
            
            if acceptInnerBody then
                pinnerExpr () <|> ptrueExpr () <|> pfalseExpr () <|> peqExpr () <|> pgrExpr () <|> pleExpr ()
            else
                ptrueExpr () <|> pfalseExpr () <|> peqExpr () <|> pgrExpr () <|> pleExpr ()
        attempt <| _pbody true()
    
    let prule () = pipe4 (psignature () .>> ws) (pstring ":-" .>> ws) (pbody ()) (pstring ".") (fun signature _ body _ -> Rule(signature, body))

    let pdef () = (pstring ":-" .>> ws) >>. (pfact () <|> prule ()) |>> RuleParseResult

    let pquery () = (pstring "?-" .>> ws) >>. psignature () .>> (pstring ".") |>> (fun (Signature(n, l)) -> CallParseResult(CallExpression(GoalSignature(n, toArgs <| fromParams l))))

    let pinteractive () = pquery () <|> pdef ()

module Parse =
    open Prims

    let convertResult = function
       | Success(r, _, _) -> r
       | Failure(e, _, _) -> ParseError e

    let testRun parser str =
        run parser str

    let testRunConvert parser str =
        run parser str
        |> convertResult

    let parsePlString str =
        run (pinteractive ()) str
        |> convertResult
    
    // UTF8 is the default, but it will detect UTF16 or UTF32 byte-order marks automatically
    let parsePlFile fileName encoding =
    #if PCL_FPARSEC
        runParserOnString json () fileName (System.IO.File.ReadAllText(fileName, encoding))
        |> convertResult
    #else
        runParserOnFile (pinteractive ()) () fileName encoding
        |> convertResult
    #endif
    
    let parsePlStream stream encoding =
        runParserOnStream (pinteractive ()) () "" stream System.Text.Encoding.UTF8
        |> convertResult
