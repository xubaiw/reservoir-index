import BuildSystems.Rule
import BuildSystems.Trace

def Rebuilder
  (c     : (Type _ → Type _) → Type _)
  (i k v : Type _)
:= k
 → v
 → Rule c k v
 → Rule (MonadState i) k v

def vtRebuilder
  [BEq k]
  [Hashable v]
  : Rebuilder Monad (VT k v) k v
:= sorry

def ctRebuilder
  [BEq k]
  [Hashable v]
  : Rebuilder Monad (CT k v) k v
:= sorry

def dctRebuilder
  [BEq k]
  [Hashable v]
  : Rebuilder Monad (DCT k v) k v
:= sorry
