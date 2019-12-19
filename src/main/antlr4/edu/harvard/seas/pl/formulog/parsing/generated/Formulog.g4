grammar Formulog;

prog
:
	(
		metadata
		| stmt
	)* EOF
;

tsvFile
:
	tabSeparatedTermLine* EOF
;

tabSeparatedTermLine
:
	(term (TAB term)*)? NEWLINE	
;

// Program metadata ////////////////////////////////////////////////////////////

metadata
:
	funDefs '.'? # funDecl
	| annotation* relType =
	(
		INPUT
		| OUTPUT
	) ID typeList '.'? # relDecl
	| 'type' typeDefLHS EQ type '.'? # typeAlias
	| 'type' typeDefLHS EQ typeDefRHS
	(
		'and' typeDefLHS EQ typeDefRHS
	)* '.'? # typeDecl
	| 'uninterpreted' 'fun' constructorType ':' type '.'? # uninterpFunDecl
	| 'uninterpreted' 'sort' typeDefLHS '.'? # uninterpSortDecl
;

funDefLHS
:
	ID args = varTypeList ':' retType = type
;

funDefs
:
	'fun' funDefLHS EQ term
	(
		'and' funDefLHS EQ term
	)*
;

constructorType
:
	ID typeList
;

varTypeList
:
	'(' VAR ':' type
	(
		',' VAR ':' type
	)* ')'
	| // can be empty

;

typeList
:
	'(' type
	(
		',' type
	)* ')'
	| // can be empty

;

type0
:
	'(' type ')' # parenType
	| TYPEVAR # typeVar
	| type0 ID index # typeRef
	| (
		'(' type
		(
			',' type
		)* ')'
	)? ID index # typeRef
;

type
:
	type0
	(
		'*' type0
	)* # tupleType
;

index
:
	'[' INT
	(
		',' INT
	)* ']'
	| // can be empty

;

typeDefLHS
:
	(
		TYPEVAR
		| '(' TYPEVAR
		(
			',' TYPEVAR
		)* ')'
	)? ID
;

typeDefRHS
:
	adtDef
	| recordDef
;

adtDef
:
	'|'? constructorType
	(
		'|' constructorType
	)*
	| // can be empty

;

recordDef
:
	'{' recordEntryDef
	(
		';' recordEntryDef
	)* ';'? '}'
;

recordEntryDef
:
	ID ':' type
;

annotation
:
	'@' ID
;

// Program logic ///////////////////////////////////////////////////////////////

stmt
:
	clause # clauseStmt
	| fact # factStmt
	| query # queryStmt
;

clause
:
	head = nonEmptyTermList ':-' body = nonEmptyTermList '.'
;

fact
:
	term '.'
;

query
:
	':-' term '.'
;

predicate
:
	ID termArgs
;

functor
:
	id =
	(
		ID
		| XID
	) index termArgs # indexedFunctor
;

termArgs
:
	(
		'('
		(
			term
			(
				',' term
			)*
		) ')'
	)?
;

term
:
	HOLE # holeTerm
	| 'smt_eq' '[' type ']' termArgs # smtEqTerm
	| 'fold' '[' ID ']' termArgs # foldTerm
	| functor # functorTerm
	| list # listTerm
	| tuple # tupleTerm
	| '(' term ')' # parensTerm
	| op =
	(
		MINUS
		| BANG
	) term # unopTerm
	| term op =
	(
		MUL
		| DIV
		| REM
	) term # binopTerm
	| term op =
	(
		PLUS
		| MINUS
	) term # binopTerm
	| < assoc = right > term '::' term # consTerm
	| term op =
	(
		LT
		| LTE
		| GT
		| GTE
	) term # binopTerm
	| term op =
	(
		EQ
		| NEQ
	) term # binopTerm
	| term op = AMP term # binopTerm
	| term op = CARET term # binopTerm
	| term op = AMPAMP term # binopTerm
	| term op = BARBAR term # binopTerm
	| VAR # varTerm
	| QSTRING # stringTerm
	| val =
	(
		INT
		| HEX
	) # i32Term
	| val = I64 # i64Term
	| val = FP64 # doubleTerm
	| val = FP32 # floatTerm
	| val =
	(
		FP32_NAN
		| FP32_POS_INFINITY
		| FP32_NEG_INFINITY
		| FP64_NAN
		| FP64_POS_INFINITY
		| FP64_NEG_INFINITY
	) # specialFPTerm
	| '{' recordEntries '}' # recordTerm
	| '{' term 'with' recordEntries '}' # recordUpdateTerm
	| '`' term '`' # formulaTerm
	| id =
	(
		XID
		| XVAR
	) '[' type ']' # constSymFormula
	| '#' '{' term '}' '[' type ']' # termSymFormula
	| NOT term # notFormula
	| < assoc = left > term op = FORMULA_EQ term # binopFormula
	| < assoc = right > term op = AND term # binopFormula
	| < assoc = right > term op = OR term # binopFormula
	| < assoc = right > term op = IMP term # binopFormula
	| < assoc = right > term op = IFF term # binopFormula
	| '#let' term EQ term 'in' term # letFormula
	| quantifier =
	(
		FORALL
		| EXISTS
	) variables = nonEmptyTermList
	(
		':' pattern = nonEmptyTermList
	)? '.' boundTerm = term # quantifiedFormula
	| '#if' term 'then' term 'else' term # iteTerm
	| term ISNOT ID # outermostCtor
	| 'match' term 'with' '|'? matchClause
	(
		'|' matchClause
	)* 'end' # matchExpr
	| 'let' lhs = letBind '=' assign = term 'in' body = term # letExpr
	| 'let' funDefs 'in' letFunBody = term # letFunExpr
	| 'if' guard = term 'then' thenExpr = term 'else' elseExpr = term # ifExpr
;

recordEntries
:
	recordEntry
	(
		';' recordEntry
	)* ';'?
;

recordEntry
:
	ID '=' term
;

letBind
:
	(
		term
		| '(' term ',' term
		(
			',' term
		)* ')'
	)
;

nonEmptyTermList
:
	term
	(
		',' term
	)*
;

list
:
	'['
	(
		term
		(
			',' term
		)*
	)? ']'
;

tuple
:
	'(' term ',' term
	(
		',' term
	)* ')'
;

matchClause
:
	pats = patterns '=>' rhs = term
;

patterns
:
	term
	(
		'|' term
	)*
;

// Tokens //////////////////////////////////////////////////////////////////////

AND
:
	'/\\'
;

OR
:
	'\\/'
;

IMP
:
	'==>'
;

IFF
:
	'<==>'
;

NOT
:
	'~'
;

FORMULA_EQ
:
	'#='
;

INPUT
:
	'input'
;

OUTPUT
:
	'output'
;

FP32_NAN
:
	'fp32_nan'
;

FP32_POS_INFINITY
:
	'fp32_pos_infinity'
;

FP32_NEG_INFINITY
:
	'fp32_neg_infinity'
;

FP64_NAN
:
	'fp64_nan'
;

FP64_POS_INFINITY
:
	'fp64_pos_infinity'
;

FP64_NEG_INFINITY
:
	'fp64_neg_infinity'
;

TYPEVAR
:
	'\'' ID
;

XVAR
:
	'#' VAR
;

VAR
:
	[A-Z_] [a-zA-Z0-9_]*
;

INT
:
	(
		'+'
		| '-'
	)? [0-9]+
;

HEX
:
	'0x' [0-9a-fA-F]+
;

fragment
FP
:
	(
		INT '.' [0-9]+
		|
		(
			'+'
			| '-'
		)? '.' [0-9]+
	)
	(
		(
			'E'
			| 'e'
		) [0-9]+
	)?
;

fragment
FPE
:
	(
		FP
		| INT
	)
	(
		'e'
		| 'E'
	) INT
;

FP32
:
	(
		FP
		| INT
		| FPE
	)
	(
		'F'
		| 'f'
	)
;

FP64
:
	(
		FP
		| FPE
	)
	(
		'D'
		| 'd'
	)?
	| INT
	(
		'D'
		| 'd'
	)
;

I64
:
	(
		INT
		| HEX
	)
	(
		'L'
		| 'l'
	)
;

LT
:
	'<'
;

LTE
:
	'<='
;

GT
:
	'>'
;

GTE
:
	'>='
;

MUL
:
	'*'
;

DIV
:
	'/'
;

REM
:
	'%'
;

PLUS
:
	'+'
;

MINUS
:
	'-'
;

BANG
:
	'!'
;

CARET
:
	'^'
;

AMP
:
	'&'
;

BARBAR
:
	'||'
;

AMPAMP
:
	'&&'
;

ISNOT
:
	'not'
;

EQ
:
	'='
;

NEQ
:
	'!='
;

FORALL
:
	'forall'
;

EXISTS
:
	'exists'
;

HOLE
:
	'??'
;

NEWLINE
:
	('\r\n' | [\n\r]) -> channel(HIDDEN)
;

TAB
:
	'\t' -> channel(HIDDEN)
;

SPACES
:
	[ ]+ -> skip
;

COMMENT
:
	'(*'
	(
		COMMENT
		| .
	)*? '*)' -> skip
;

XID
:
	'#' ID
;

ID
:
	[a-z] [a-zA-Z0-9_]*
;

fragment
ESCAPE
:
	'\\' .
;

QSTRING
:
	'"'
	(
		ESCAPE
		| ~( '\n' | '\r' | '"' | '\\' )
	)* '"'
;