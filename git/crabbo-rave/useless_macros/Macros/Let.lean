syntax binder := ident " := " term
syntax "let" binder,+ " in " term : term
syntax "let*" binder,+ " in " term : term

macro_rules
  | `(let $name:ident := $v:term in $t:term) => `(let $name := $v; $t)
  | `(let* $name:ident := $v:term in $t:term) => `(let rec $name:ident := $v; $t)
  | `(let $name:ident := $v:term, $bs:binder,* in $t:term) =>
    `(let $name := $v; let $bs:binder,* in $t:term)
  | `(let* $name:ident := $v:term, $bs:binder,* in $t:term) =>
    `(let rec $name:ident := $v; let* $bs:binder,* in $t:term)