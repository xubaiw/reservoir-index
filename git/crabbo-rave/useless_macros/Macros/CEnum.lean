syntax "enum" ident "{" sepBy(ident, ",") "}" ";": command 

macro_rules 
  | `(enum $name:ident { $[$ids:ident],* };) =>
    `(inductive $name where $[| $ids:ident]*)
    