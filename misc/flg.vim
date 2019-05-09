" Vim syntax file
" Language: FormuLog
" Maintainer: Aaron Bembenek
" Latest Revision: 9 May 2019

if exists("b:current_syntax")
    finish
endif

syn match number "\v<[0-9]+(\.[0-9]*)*[lLfFdD]?>"
syn match number "\v<[0-9]*\.[0-9]+[lLfFdD]?>"
syn match keywords "`"
syn match keywords ":-"
syn match keywords "\~"
syn match keywords "#="
syn match keywords '::'
syn match keywords "|"
syn match keywords "&"
syn match keywords "+"
syn match keywords "-"
syn match keywords "*"
syn match keywords "/"
syn match keywords "\\"
syn match keywords "!"
syn match keywords "="
syn match keywords "<"
syn match keywords ">"
syn match keywords ","
syn match keywords "\."
syn keyword keywords type fun constructor input output match let if then else end fun in with uninterpreted and sort
syn keyword todo contained TODO XXX FIXME
syn region comment start="(\*" end="\*)" fold contains=todo,comment
syn keyword typeKeywords i32 i64 fp32 fp64 list bool option cmp string smt bv fp sym 
syn match variable "\v<[A-Z_][a-zA-Z0-9_]*>"
syn match solverSymbol "#\v<[a-zA-Z0-9_]+>"
syn match solverSymbol "#{"
syn match solverSymbol "}"
syn match keywords "#let"
syn match keywords "#if"
syn region string start=/\v"/ skip=/\v\\./ end=/\v"/
let b:current_syntax = "flg"

hi def link number          Constant
hi def link string          Constant
hi def link keywords        Statement
hi def link comment         Comment 
hi def link typeKeywords    Type
hi def link variable        Identifier 
hi def link todo            Todo 
hi def link solverSymbol    Identifier
