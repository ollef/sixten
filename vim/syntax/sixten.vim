" Syntax highlighting for Sixten

if exists("b:current_syntax")
  finish
endif

highlight def link sixtenIdentifier Identifier
highlight def link sixtenType Type
highlight def link sixtenDefinition Function
highlight def link sixtenNumber Number
highlight def link sixtenString String
highlight def link sixtenModuleKeyword Keyword
highlight def link sixtenClassKeyword Keyword
highlight def link sixtenModifierKeyword Keyword
highlight def link sixtenTypeKeyword Keyword
highlight def link sixtenLetKeyword Keyword
highlight def link sixtenCaseKeyword Conditional
highlight def link sixtenForall Keyword
highlight def link sixtenLambda Keyword
highlight def link sixtenDot Keyword
highlight def link sixtenArrow Operator
highlight def link sixtenEquals Operator
highlight def link sixtenConstraintArrow Operator
highlight def link sixtenTypeAnno Operator
highlight def link sixtenPipe Operator
highlight def link sixtenLineComment Comment
highlight def link sixtenBlockComment Comment
highlight def link sixtenTodo Todo
highlight def link sixtenExternQuotes Operator

syn match sixtenIdentifier "[_a-z][a-zA-Z0-9_']*" contained
syn match sixtenType "\<[A-Z][a-zA-Z0-9_']*\>"
syn match sixtenDefinition "^\s*\([_a-zA-Z][a-zA-Z0-9_']*\_s*\)\+:"
syn match sixtenNumber "\<[0-9]\+\>"
syn region sixtenString start=+"+ skip=+\\\\\|\\"+ end=+"+
  \ contains=@Spell
syn keyword sixtenModuleKeyword import module as exposing
syn keyword sixtenClassKeyword instance class
syn keyword sixtenModifierKeyword abstract
syn keyword sixtenTypeKeyword type where
syn keyword sixtenCaseKeyword case of
syn keyword sixtenLetKeyword let in
syn keyword sixtenForall forall
syn match sixtenLambda "\\"
syn match sixtenDot "\."
syn match sixtenArrow "->"
syn match sixtenEquals "="
syn match sixtenConstraintArrow "=>"
syn match sixtenTypeAnno ":"
syn match sixtenPipe "|"

syn match sixtenLineComment "---*\([^-!#$%&\*\+./<=>\?@\\^|~].*\)\?$"
  \ contains=
  \ sixtenTodo,
  \ @Spell
syn region sixtenBlockComment start="{-" end="-}"
  \ contains=
  \ sixtenBlockComment,
  \ sixtenTodo,
  \ @Spell

syn keyword sixtenTodo TODO FIXME contained

function! IncludeFileTypeAsGroup(filetype, groupName) abort
  if exists('b:current_syntax')
    let s:current_syntax=b:current_syntax
    " Remove current syntax definition, as some syntax files (e.g. cpp.vim)
    " do nothing if b:current_syntax is defined.
    unlet b:current_syntax
  endif
  execute 'syn include @'.a:groupName.' syntax/'.a:filetype.'.vim'
  try
    execute 'syn include @'.a:groupName.' after/syntax/'.a:filetype.'.vim'
  catch
  endtry
  if exists('s:current_syntax')
    let b:current_syntax=s:current_syntax
  else
    unlet b:current_syntax
  endif
endfunction

call IncludeFileTypeAsGroup('c', 'CSyntax')

syn region sixtenExternC matchgroup=sixtenExternQuotes start="(C|" end="|)" keepend contains=@CSyntax
