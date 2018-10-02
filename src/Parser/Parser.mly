%{
  open Abbrevs
  open Expressions
  open Eval
  open EvalTypes
%}

%token EOF
%token DOT
%token LPAR
%token RPAR
%token LCURLY
%token RCURLY
%token PLUS
%token MINUS
%token EXCLAM
%token COMMA
%token COLON
%token SEMICOLON
%token CARET
%token UNDERSCORE
%token EQ
%token INEQ
%token AND

%token SIMPLIFY
%token UNIFY
%token DEDUCE
%token STATICE
%token KNOWLEDGE
%token UNIVERSAL
%token SEARCH

%token INDCPA
%token INDCCA
%token INDIFF

%token NAMES
%token WITH
%token FROM
%token VS
%token ALIAS

%token ROUNDS
%token ORACLE
%token DISTINGUISHER
%token INVERTIBLE
%token RETURN
%token ASSERT
%token LEFTARROW
%token DOLLAR
%token BITSTRING
%token PROBCHOICE
%token BEGIN
%token END
%token CASE

%token VAR
%token ZERO
%token ONE

%token <int> INT
%token <string> NAME

/************************************************************************/
/* Priority & associativity */

%left PLUS

/************************************************************************/
/* Production types */

%type <Eval.command list> cmds_t
%type <EvalTypes.primitive> attack_search

/************************************************************************/
/* Start productions */

%start cmds_t
%start attack_search

%%

/************************************************************************/
/* Types */

idx :
| UNDERSCORE; ONE;      { 0 }
| UNDERSCORE; i = INT;  { i-1 }

inverse :
| CARET; MINUS; ONE;                 { NEG }
| CARET; LPAR; MINUS; ONE; RPAR;     { NEG }
| CARET; LCURLY; MINUS; ONE; RCURLY; { NEG }

invertible :
| EXCLAM;                       { false }

expression:
| ZERO;                       { Zero }
| c = NAME;                   { Const(c) }
| VAR; LPAR; x = NAME; RPAR;  { Var(x) }
| VAR; x = NAME;              { Var(x) }
| n = NAME; inv = invertible?; is_inv = inverse?; i = idx?;
   LPAR; left = separated_list(COMMA, expression); SEMICOLON;
         right = separated_list(COMMA, expression); RPAR;
    { F(n, (optional ~d:0 i), (optional ~d:POS is_inv), (left, right), (optional ~d:true inv), false, None) }
| n = NAME; inv = invertible?; is_inv = inverse?; i = idx?;
    LPAR; right = separated_list(COMMA, expression); RPAR;
    { F(n, (optional ~d:0 i), (optional ~d:POS is_inv), ([], right), (optional ~d:true inv), false, None) }
| e1 = expression; PLUS; e2 = expression;  { XOR([e1;e2]) }
| LPAR; e = expression; RPAR;              { e }

is_eq :
| EQ     { Eq }
| INEQ   { Ineq }

equation :
| e1 = expression; c = is_eq; e2 = expression;
     { if is_zero e1 then (c,e2) else if is_zero e2 then (c,e1) else (c,XOR([e1; e2])) }

unif_problem :
| eqs = separated_list(AND, equation);    { make_unif_problem eqs }

frame:
| LCURLY; exprs = separated_list(COMMA, expression); RCURLY; WITH;
    NAMES; EQ; LCURLY; names = separated_list(COMMA, NAME); RCURLY;  { make_frame (exprs, names) }

rounds:
| ROUNDS; funs = separated_list(COMMA, NAME); DOT;               { L.map funs ~f:(fun f -> (f,false)) }
| ROUNDS; funs = separated_list(COMMA, NAME); INVERTIBLE; DOT;   { L.map funs ~f:(fun f -> (f,true)) }

assignment:
| v = NAME; EQ; e = expression; SEMICOLON; { (v,e) }

with_alias:
| WITH; ALIAS; a = NAME;             { a }

oracle:
| ORACLE; n = NAME; is_inv = inverse?; a = with_alias?; LPAR; args = separated_list(COMMA, NAME); RPAR; COLON; EQ;
   assignments = list(assignment); RETURN; out = separated_list(COMMA, expression); DOT; { (n, (optional ~d:POS is_inv), a, args, assignments, out) }

dist_cmd:
| v = NAME; LEFTARROW; DOLLAR; BITSTRING;                              { DistCmdSamp(v) }
| v = NAME; EQ; e = expression;                                        { DistCmdAssign(v,e) }
| v = NAME; LEFTARROW; f = NAME; is_inv = inverse?;
     i = idx? LPAR; exprs = separated_list(COMMA, expression); RPAR;   { DistCmdSimQuery(v,f,(optional ~d:POS is_inv),(optional ~d:0 i),exprs) }
| ASSERT; eq = equation;                                               { DistCmdAssert(eq) }

case:
| CASE; COLON; { () }

dist_program:
| cmd = dist_cmd; SEMICOLON; p = dist_program      { DistProgCmd(cmd,p) }
| BEGIN; PROBCHOICE; COLON; case; ps = separated_list(case, dist_program); END;    { DistProgChoice(ps) }
| RETURN; ONE; SEMICOLON?                          { DistProgReturn }


cmd :
| SIMPLIFY;  e = expression; DOT;                                    { Simplify(e) }
| UNIFY;     u = unif_problem; DOT;                                  { Unify(u) }
| DEDUCE;    e = expression; FROM; f = frame; DOT;                   { Deduce(e,f) }
| STATICE;   f1 = frame; VS; f2 = frame; DOT;                        { StaticE(f1,f2) }
| KNOWLEDGE; e = separated_list(COMMA,expression);
    FROM; f = separated_list(COMMA,frame); DOT;                      { Knowledge(e,f) }
| UNIVERSAL; LCURLY; rs = list(rounds); os = list(oracle);
    DISTINGUISHER; COLON; EQ; p = dist_program; DOT; RCURLY; DOT;    { IsUniversal(rs |> L.concat, os, p) }

cmds_t : cs = list(cmd); EOF;   { cs };

attack_type:
| INDCPA   { 0 }
| INDCCA   { 1 }
| INDIFF   { 2 }

attack_search:
| SEARCH; t = attack_type; LCURLY; rs = list(rounds); os = list(oracle); RCURLY; DOT; { (t, rs |> L.concat,os) }
