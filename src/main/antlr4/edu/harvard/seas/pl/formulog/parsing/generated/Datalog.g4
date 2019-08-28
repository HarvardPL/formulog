grammar Datalog;

prog
:
	(
		metadata
		| stmt
	)* EOF
;

// Program metadata ////////////////////////////////////////////////////////////

metadata
:
	'fun' funDefLHS EQ term
	(
		'and' funDefLHS EQ term
	)* '.'? # funDecl
	| annotation* relType =
	(
		INPUT
		| OUTPUT
	) ID aggTypeList '.'? # relDecl
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

aggType
:
	type
	(
		'<' func = ID ',' unit = term '>'
	)?
;

aggTypeList
:
	'(' aggType
	(
		',' aggType
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

type
:
	(
		'(' type
		(
			',' type
		)* ')'
	)? ID index # typeRef
	| type ID index # typeRef
	| TYPEVAR # typeVar
	| '(' type '*' type
	(
		'*' type
	)* ')' # tupleType
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
	head = atomList ':-' body = atomList '.'
;

atomList
:
	atom
	(
		',' atom
	)*
;

fact
:
	atom '.'
;

atom
:
	predicate # normalAtom
	| '!' predicate # negatedAtom
	| term EQ term # unification
	| term NEQ term # disunification
	| term # termAtom
;

query
:
	':-' atom '.'
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
	'<[' ID ']>' # reifyTerm
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
	| < assoc = right > term '::' term # consTerm
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
	| ',' term # unquoteTerm
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

FP32
:
	(
		FP
		| INT
	)
	(
		'F'
		| 'f'
	)
;

FP64
:
	FP
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

WS
:
	[ \t\r\n]+ -> skip
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