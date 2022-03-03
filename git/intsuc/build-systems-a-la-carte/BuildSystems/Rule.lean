set_option checkBinderAnnotations false in
structure Rule
  (c   : (Type _ → Type _) → Type _)
  (k v : Type _)
where
  run [c f]
    : (f     : Type _ → Type _)
    → (fetch : k → f v)
    → f v

def Rules
  (c   : (Type _ → Type _) → Type _)
  (k v : Type _)
:= k
 → Option (Rule c k v)
