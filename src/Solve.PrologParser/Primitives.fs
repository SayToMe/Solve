namespace Solve.PrologParser

open Solve
open Solve.Rule.Transformers

open FParsec

open Solve.TermTypes

open Solve.Rule

type ParseResult =
    | RuleParseResult of Rule
    | CallParseResult of Expression
    | ParseError of string

module Primitives =
    let ws = spaces // skips any whitespace
    let str = pstring

    let (<!>) (p: Parser<_,_>) label : Parser<_,_> =
        fun stream ->
            let initialPosition = stream.Position
            let initToken = stream.IndexToken
            printfn "%A: Entering %s" stream.Position label
            let reply = p stream
            let resPosition = stream.Position
            stream.Seek initToken
            let str = stream.ReadCharsOrNewlines(int <| resPosition.Index - initialPosition.Index, false)
            printfn "%A: Leaving %s (%A). Res: %A, Catched (%A)" stream.Position label reply.Status (reply.Result) (str)
            reply

    let listBetweenStrings sOpen sClose pElement f =
        between (str sOpen) (str sClose)
                (ws >>. sepBy (pElement .>> ws) (str "," .>> ws) |>> f)
    
    let listBetweenStringsCustom sOpen sClose separatorParser pElement f =
        pipe3 (sOpen .>> ws) (ws >>. sepBy (pElement .>> ws) (separatorParser .>> ws)) (sClose .>> ws) f

    let ptrue = stringReturn "true"  (TypedTerm <| TypedBoolTerm(BoolTerm(true)))
    let pfalse = stringReturn "false" (TypedTerm <| TypedBoolTerm(BoolTerm(false)))
    let pnil = stringReturn "[]" (ListTerm <| NilTerm)
    let pnumber = pint32 |>> (TypedTerm << TypedNumberTerm << NumberTerm << float)
    let pchar = attempt <| str "'" >>. anyChar .>> str "'" |>> (TypedTerm << TypedCharTerm << CharTerm)

    let patomPlain =
        let isIdentifierFirstChar c = isLetter c && not(isUpper c)
        let isIdentifierChar c = isLetter c || isDigit c || c = '_'
    
        many1Satisfy2L isIdentifierFirstChar isIdentifierChar "identifier"
        .>> spaces
    let patom =
        patomPlain
        |>> (TypedTerm << TypedAtomTerm << AtomTerm)
    let pvariablePlain =
        let isIdentifierFirstChar c = isLetter c && isUpper c
        let isIdentifierChar c = isLetter c || isDigit c || c = '_'
    
        many1Satisfy2L isIdentifierFirstChar isIdentifierChar "identifier"
        .>> spaces
    let pvariable =
        pvariablePlain
        |>> (VariableTerm << Variable)
 
    let pterm = 
        let _pterm = patom <|> pvariable <|> pnumber <|> pnil <|> pfalse <|> ptrue <|> pchar
        
        let pstructure = attempt <| pipe2 patomPlain (listBetweenStrings "(" ")" _pterm id) (fun atom terms ->
            Structure(atom, terms )) |>> StructureTerm
        let plist =
            let pempty = attempt pnil
            let pnormalList = attempt <| listBetweenStrings "[" "]" _pterm (List.rev >> List.fold (fun acc s -> TypedListTerm(s, acc)) NilTerm >> ListTerm)
            let pvariableList = attempt <| listBetweenStringsCustom (str "[") (str "|" >>. ws >>. pvariablePlain .>> ws .>> str "]") (str ",") _pterm (fun s terms var -> (VarListTerm(Variable(var)), terms |> List.rev) ||> List.fold (fun acc s -> TypedListTerm(s, acc)) |> ListTerm)

            attempt <| (pempty <|> pnormalList <|> pvariableList)
        _pterm <|> pstructure <|> plist

    let psignature =
        pipe2 patomPlain (listBetweenStrings "(" ")" pterm id) (fun atom terms ->
            Signature(atom, Transformers.toParams terms ))
        .>> ws

    let pfact = psignature .>> pstring "." |>> (fun s -> Rule(s, True))

    let pbody =
        let pcalc =
            let rec _pcalc () =
                let pval = attempt <| (pterm .>> ws) |>> Value
                let rec pinnerCalc () =
                    attempt <| (pval >>=? (fun x ->
                        (attempt <| (pstring "+" .>> ws >>. _pcalc ()) |>> (fun y -> Plus(x, y)))
                        <|>
                        (attempt <| (pstring "-" .>> ws >>. _pcalc ()) |>> (fun y -> Subsctruct(x, y)))
                        <|>
                        (attempt <| (pstring "*" .>> ws >>. _pcalc ()) |>> (fun y -> Multiply(x, y)))
                        <|>
                        (attempt <| (pstring "/" .>> ws >>. _pcalc ()) |>> (fun y -> Division(x, y)))
                    ))
                pinnerCalc () <|> pval
            attempt <| _pcalc ()
        let rec _pbody () =
            let ptrueExpr = stringReturn "true" True
            let pfalseExpr = stringReturn "false" False
            let peqExpr = attempt <| pipe3 pterm (pstring "=" .>> ws) pterm (fun a1 _ a2 -> EqExpr(a1, a2))
            let pgrExpr = attempt <| pipe3 pterm (pstring ">" .>> ws) pterm (fun a1 _ a2 -> GrExpr(a1, a2))
            let pleExpr = attempt <| pipe3 pterm (pstring "<" .>> ws) pterm (fun a1 _ a2 -> LeExpr(a1, a2))
            let calcExpr () = (attempt <| pipe3 pterm (pstring "is" .>> ws) pcalc (fun t _ c -> CalcExpr(t, c)))
            let pcallExpr () = attempt <| (psignature |>> (fun (Signature(name, parameters)) -> CallExpression(GoalSignature(name, parameters |> fromParams |> toArgs))))

            let singleExpression = (ptrueExpr <|> pfalseExpr <|> peqExpr <|> pgrExpr <|> pleExpr <|> calcExpr () <|> pcallExpr ()) .>> ws

            let pinnerExpr () = attempt <| (singleExpression >>=? (fun x ->
                ((pstring "," .>> ws) >>? _pbody () |>> (fun y -> AndExpression(x, y)))
                <|>
                ((pstring ";" .>> ws) >>? _pbody () |>> (fun y -> OrExpression(x, y)))
            ) .>> ws)

            (pinnerExpr () <|> singleExpression)

        attempt <| (_pbody () .>> ws)
    
    let prule = pipe4 psignature (pstring ":-" .>> ws) (pbody .>> ws) (pstring ".") (fun signature _ body _ -> Rule(signature, body))

    let pdef = (pstring ":-" .>> ws) >>. (attempt pfact <|> attempt prule) |>> RuleParseResult

    let pquery = (pstring "?-" .>> ws) >>. psignature .>> (pstring ".") |>> (fun (Signature(n, l)) -> CallParseResult(CallExpression(GoalSignature(n, toArgs <| fromParams l))))

    let pcommand: Parser<ParseResult, unit> = (attempt pquery) <|> (attempt pdef)
