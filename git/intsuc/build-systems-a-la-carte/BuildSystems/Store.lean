structure Store
  (i k v : Type _)
where
  info   : i
  values : k → v

abbrev Hash (α : Type _) := α

def Store.getValue
  (store : Store i k v)
  (key   : k)
  : v
:= store.values key

def Store.getHash
  [Hashable v]
  (store : Store i k v)
  (key   : k)
  : Hash v
:= store.getValue key
