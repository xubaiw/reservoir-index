syntax binder' := ident " : " term
syntax "def" ident "(" sepBy(binder', ",") ")" " -> " term " : " term : command

macro_rules
  | `(def $f:ident ($a:ident : $ty:term) -> $ty':term: $v:term) =>
    `(def $f:ident : ($ty:term -> $ty':term) := fun $a:ident => $v:term)
  | `(def $f:ident ($bs:binder',*, $a:ident : $ty:term) -> $ty':term: $v:term) =>
    `(def $f:ident ($bs:binder',*) -> ($ty:term -> $ty':term) : fun $a:ident => $v:term)