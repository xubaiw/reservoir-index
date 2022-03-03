import BuildSystems.Build
import BuildSystems.Rebuilder

def Scheduler
  (c       : (Type _ → Type _) → Type _)
  (i j k v : Type _)
:= Rebuilder c j k v
 → Build c i k v

def topological
  [Ord k]
  : Scheduler Applicative i i k v
:= sorry

def restarting
  [Ord k]
  : Scheduler Monad (i × List k) i k v
:= sorry

def suspending
  [Ord k]
  : Scheduler Monad i i k v
:= sorry
