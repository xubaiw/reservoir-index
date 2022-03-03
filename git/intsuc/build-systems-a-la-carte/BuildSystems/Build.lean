import BuildSystems.Rule
import BuildSystems.Store

def Build
  (c     : (Type _ → Type _) → Type _)
  (i k v : Type _)
:= Rules c k v
 → k
 → Store i k v
 → Store i k v
