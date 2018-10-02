{
  open Parser

  exception Error of string

  let unterminated_comment () = raise (Error "unterminated comment")
  let unterminated_string  () = raise (Error "unterminated string")
}

let blank = [' ' '\t' '\r' '\n']
let newline = '\n'
let letters = ['a'-'z' 'A'-'Z']
let alphanum = ['a'-'z' 'A'-'Z' '0'-'9' '\'']

rule lex = parse
  | blank+  { lex lexbuf }
  | "(*"    { comment lexbuf; lex lexbuf }
  | newline { Lexing.new_line lexbuf; lex lexbuf }
  | eof     { EOF }
  | "."     { DOT }
  | "("     { LPAR }
  | ")"     { RPAR }
  | "{"     { LCURLY }
  | "}"     { RCURLY }
  | "+"     { PLUS }
  | "-"     { MINUS }
  | "!"     { EXCLAM }
  | ","     { COMMA }
  | ":"     { COLON }
  | ";"     { SEMICOLON }
  | "^"     { CARET }
  | "_"     { UNDERSCORE }
  | "="     { EQ }
  | "<>"    { INEQ }
  | "/\\"   { AND }

  | "simplify"      { SIMPLIFY }
  | "unify"         { UNIFY }
  | "deduce"        { DEDUCE }
  | "static-eq"     { STATICE }
  | "knowledge"     { KNOWLEDGE }
  | "is_universal"  { UNIVERSAL }
  | "search_attack" { SEARCH }

  | "INDCPA"        { INDCPA }
  | "INDCCA"        { INDCCA }
  | "Indiff"        { INDIFF }

  | "rounds"        { ROUNDS }
  | "oracle"        { ORACLE }
  | "distinguisher" { DISTINGUISHER }
  | "invertible"    { INVERTIBLE }
  | "return"        { RETURN }
  | "assert"        { ASSERT }
  | "<-"            { LEFTARROW }
  | "$"             { DOLLAR }
  | "{0,1}^n"       { BITSTRING }
  | "prob choice"   { PROBCHOICE }
  | "begin"         { BEGIN }
  | "end"           { END }
  | "case"          { CASE }

  | "names"        { NAMES }
  | "with"         { WITH }
  | "from"         { FROM }
  | "vs"           { VS }
  | "alias"        { ALIAS }

  | "Var"   { VAR }
  | "0"     { ZERO }
  | "1"     { ONE }

  | ['0'-'9']['0'-'9']* as s { INT(int_of_string(s)) }
  | letters alphanum* as s   { NAME s }

and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | newline     { Lexing.new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }
