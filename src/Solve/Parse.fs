namespace Solve

open Solve
open FParsec

open Solve.TermTypes

open Solve.Rule

type ParseResult =
    | RuleParseResult of Rule
    | CallParseResult of Goal
    | ParseError of string

module Prims =
    let ws = spaces // skips any whitespace
    let str = pstring    

    let listBetweenStrings sOpen sClose pElement f =
        between (str sOpen) (str sClose)
                (ws >>. sepBy (pElement .>> ws) (str "," .>> ws) |>> f)
    
    let ptrue  = stringReturn "true"  (TypedTerm <| TypedBoolTerm(BoolTerm(true)))
    let pfalse = stringReturn "false" (TypedTerm <| TypedBoolTerm(BoolTerm(false)))
    let pnil = stringReturn "[]" (ListTerm <| NilTerm)
    let pnumber = pfloat |>> (fun x -> (TypedTerm << TypedNumberTerm << NumberTerm) <| x)
    let pchar = anyChar |>> (TypedTerm << TypedCharTerm << CharTerm)

    let patomPlain =
        let isIdentifierFirstChar c = isLetter c && not(isUpper c)
        let isIdentifierChar c = isLetter c || isDigit c || c = '_'
    
        many1Satisfy2L isIdentifierFirstChar isIdentifierChar "identifier"
        .>> spaces
    let patom =
        patomPlain
        |>> (TypedTerm << TypedAtomTerm << AtomTerm)
    let pvariable =
        let isIdentifierFirstChar c = isLetter c && isUpper c
        let isIdentifierChar c = isLetter c || isDigit c || c = '_'
    
        many1Satisfy2L isIdentifierFirstChar isIdentifierChar "identifier"
        .>> spaces
        |>> (VariableTerm << Variable)
    
    // todo add lists and structure to terms(?)
    let pterm = patom <|> pvariable <|> pnumber <|> pchar <|> pnil <|> pfalse <|> ptrue
    let pstructurePlain = pipe2 patomPlain (listBetweenStrings "(" ")" pterm id) (fun atom terms ->
        Structure(atom, terms ))
    let pstructure = pstructurePlain |>> StructureTerm
    let plist = listBetweenStrings "[" "]" pterm (fun x -> (NilTerm, x) ||> List.fold (fun acc s -> TypedListTerm(s, acc)) |> ListTerm)

    let psignature = pipe2 patomPlain (listBetweenStrings "(" ")" pterm id) (fun atom terms ->
        Signature(atom, Transformers.toParams terms ))

    let pfact = psignature |>> (fun s -> Rule(s, True))

    let pbody =
        let pcalc =
            let rec _pcalc() =
                let pval = pterm |>> Value
                let plus = pipe3 (_pcalc()) (pstring "+") (_pcalc()) (fun c1 _ c2 -> Plus(c1, c2))
                pval <|> plus
            _pcalc()
        let rec _pbody() =
            let ptrueExpr = stringReturn "true" True
            let pfalseExpr = stringReturn "false" False
            let pandExpr = pipe3 (_pbody()) (pstring ",") (_pbody()) (fun expr1 _ expr2 -> AndExpression(expr1, expr2))
            let porExpr = pipe3 (_pbody()) (pstring ";") (_pbody()) (fun expr1 _ expr2 -> OrExpression(expr1, expr2))
            let peqExpr = pipe3 pterm (pstring "=") pterm (fun a1 _ a2 -> EqExpr(a1, a2))
            let pgrExpr = pipe3 pterm (pstring ">") pterm (fun a1 _ a2 -> GrExpr(a1, a2))
            let pleExpr = pipe3 pterm (pstring "<") pterm (fun a1 _ a2 -> LeExpr(a1, a2))
            let calcExpr = pipe3 pterm (pstring "is") pcalc (fun t _ c -> CalcExpr(t, c))
            
            ptrueExpr <|> pfalseExpr <|> pandExpr <|> porExpr <|> peqExpr <|> pgrExpr <|> pleExpr
        _pbody()
    
    let prule = pipe2 psignature pbody (fun signature body -> Rule(signature, body))

    let pdef = (pstring ":-" >>. (pfact <|> prule) .>> pstring ".") |>> RuleParseResult

    let pquery = (pstring "?-" >>. pstructurePlain .>> pstring ".") |>> (CallParseResult << Goal)

    let pinteractive = pquery <|> pdef

module Parse =
    open Prims

    let convertResult = function
       | Success(r, _, _) -> r
       | Failure(e, _, _) -> ParseError e

    let testRun parser str = run parser str

    let floatp = pfloat

    let oper = (|>>)

    let parsePlString str =
        run pinteractive str
        |> convertResult
    
    // UTF8 is the default, but it will detect UTF16 or UTF32 byte-order marks automatically
    let parsePlFile fileName encoding =
    #if PCL_FPARSEC
        runParserOnString json () fileName (System.IO.File.ReadAllText(fileName, encoding))
        |> convertResult
    #else
        runParserOnFile pinteractive () fileName encoding
        |> convertResult
    #endif
    
    let parsePlStream stream encoding =
        runParserOnStream pinteractive () "" stream System.Text.Encoding.UTF8
        |> convertResult
